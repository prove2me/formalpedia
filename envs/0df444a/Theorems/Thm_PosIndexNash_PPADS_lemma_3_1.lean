-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lemma_3_1
-- name    : PosIndexNash.PPADS.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:32:43.837097+00:00
-- url     : https://prove2.me/theorems/c4d69387-8fc6-4f60-bfa2-d0540ef6eab6
-- title:
--   Lemma 3.1 — oriented Lemke–Howson paths: internal vertices pass through, the origin is a source of sign −1, endpoints are oriented by their Shapley index
-- statement:
--   Let $(A, B)$ be a nondegenerate rational bimatrix game with $m, n \ge 1$ and strictly positive payoffs, and let $R = P\times Q$ be its labeled product best response polytope, $d = m + n$. For every missing label $\ell$, orient the missing-$\ell$ graph by the determinant rule $t_E = (-1)^{d+1}c_E$ of (8)–(9). Then:
--
--   1. every internal (not completely labeled) vertex of the graph has exactly one incoming and exactly one outgoing edge;
--   2. the artificial equilibrium $0$ is a source (one outgoing edge, no incoming edge) and has sign $\sigma(0) = -1$;
--   3. a completely labeled vertex $v = (x, y) \ne 0$ is a source when the Shapley index of its equilibrium $(x/\mathbf 1^\top x, y/\mathbf 1^\top y)$ is $-1$ and a sink when it is $+1$.
--
--   Moreover, the predecessor and successor bases can be found in polynomial time: there are polynomial-time maps that, given the code of the game, the label $\ell$ and the basis code $\chi(u)$ of the tail of an oriented edge $u \to v$, return $\chi(v)$, and given $\chi(v)$ return $\chi(u)$:
--   $$u \to v \implies \mathrm{succ}(\langle A, B\rangle, \ell, \chi(u)) = \chi(v),\quad \mathrm{pred}(\langle A,B\rangle, \ell, \chi(v)) = \chi(u).$$
--
--   This is the signed Lemke–Howson theorem; it is what puts Positive-Index Nash in PPADS (Theorem 3.2).
--
--   Differences from the source:
--   - encoding: "computable locally from a vertex basis; the predecessor and successor bases can be found in polynomial time" → two maps computable in polynomial time on Cook's Turing machines, uniform over all games, from the string `G.enc ++ encBin ℓ ++ χ(u)` to `χ(v)` and back, correct on every oriented edge; reason: the paper's notion of polynomial time on its basis representation (18), made explicit.
--   - encoding: labels $[d] = \{1,\dots,d\}$, vertices as bases → 0-based labels `Fin (m + n)`, vertices as points of $\mathbb{R}^d$ and edges as segments that are one-dimensional faces; reason: Lean convention, same graph.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 16, Lemma 3.1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuasiStrictNE_RatGame
import Definitions.Def_QuasiStrictNE_RatGame_enc
import Definitions.Def_PosIndexNash_PPADS_Nondegenerate
import Definitions.Def_PosIndexNash_PPADS_ShapleyIndex
import Definitions.Def_PosIndexNash_PPADS_LemkeHowson

open QAlgorithms.LocalHamiltonian

namespace PosIndexNash.PPADS

theorem lemma_3_1 :
    (∀ G : QuasiStrictNE.RatGame, 1 ≤ G.m → 1 ≤ G.n →
      (∀ i j, 0 < G.A i j) → (∀ i j, 0 < G.B i j) →
      Nondegenerate (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) →
      ∀ l : Fin (G.m + G.n),
        (∀ v, InMissingGraph (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l v →
          ¬ IsCompletelyLabeled (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) v →
          (∃! w, LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l v w) ∧
          (∃! w, LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l w v)) ∧
        ((∃! w, LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l 0 w) ∧
          (¬ ∃ w, LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l w 0) ∧
          vertexSign (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) 0 = -1) ∧
        (∀ v, IsCompletelyLabeled (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) v → v ≠ 0 →
          (shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
              (lhRowStrategy v) (lhColStrategy v) = -1 →
            (∃! w, LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l v w) ∧
            ¬ ∃ w, LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l w v) ∧
          (shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
              (lhRowStrategy v) (lhColStrategy v) = 1 →
            (∃! w, LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l w v) ∧
            ¬ ∃ w, LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l v w))) ∧
    ∃ succ pred : List Bool → List Bool,
      CookPvsNP.PolyTimeComputable succ ∧ CookPvsNP.PolyTimeComputable pred ∧
      ∀ G : QuasiStrictNE.RatGame, 1 ≤ G.m → 1 ≤ G.n →
        (∀ i j, 0 < G.A i j) → (∀ i j, 0 < G.B i j) →
        Nondegenerate (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) →
        ∀ (l : Fin (G.m + G.n)) (u v : Fin (G.m + G.n) → ℝ),
          LHOriented (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) l u v →
          succ (G.enc ++ encBin l.val ++
              basisCode (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) u) =
            basisCode (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) v ∧
          pred (G.enc ++ encBin l.val ++
              basisCode (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) v) =
            basisCode (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) u := by sorry

end PosIndexNash.PPADS
