-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lh_basis_sink_circuits
-- name    : PosIndexNash.PPADS.lh_basis_sink_circuits
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:43:03.517978+00:00
-- url     : https://prove2.me/theorems/e92764cc-0880-40c7-b658-93a4569e9fd7
-- title:
--   Theorem 3.2, circuit step — normalized predecessor/successor circuits on xor basis codes
-- statement:
--   For every nondegenerate rational bimatrix game $G=(A,B)$ with $m,n\ge1$ and strictly positive payoffs, the oriented missing-$\ell$ Lemke–Howson graph can be implemented by Boolean circuits produced in polynomial time. Writing $d=m+n$ and $\chi(v)$ for the characteristic vector of the $d$ binding inequalities, the binary vertex representation is
--   $$
--   \operatorname{rep}(v)=\chi(v)\operatorname{xor}\chi(0),
--   $$
--   so the artificial equilibrium is represented by the all-zero word.
--
--   There is a polynomial-time string map $f$ and a choice of missing label $\ell$ such that $f(\langle G\rangle)$ is the code of a normalized Sink-of-Line instance $(S,P)$. Moreover, whenever $P(S(z))\ne z$, the string $z$ is $\operatorname{rep}(v)$ for a non-artificial completely labeled vertex $v$ with no outgoing oriented edge:
--   $$
--   \neg\,\exists w,\;v\to w.
--   $$
--   The quantification over all circuits with the same binary code makes explicit the self-delimiting nature of the circuit encoding. This is exactly the basis validation, invalid-string identity convention, normalization, and sink characterization in the proof of Theorem 3.2.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF), pp. 18–19, proof of Theorem 3.2, especially eq. (18)–(19); uses p. 16, Lemma 3.1

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ConstrSOSP_Circuit_eval
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_encCircuit
import Definitions.Def_PosIndexNash_PPADS_PositivePayoffNash
import Definitions.Def_PosIndexNash_PPADS_SinkOfLine
import Definitions.Def_PosIndexNash_PPADS_LemkeHowson

theorem PosIndexNash.PPADS.lh_basis_sink_circuits :
    ∃ f : List Bool → List Bool,
      CookPvsNP.PolyTimeComputable f ∧
      ∀ G : QuasiStrictNE.RatGame, 1 ≤ G.m → 1 ≤ G.n →
        (∀ i j, 0 < G.A i j) → (∀ i j, 0 < G.B i j) →
        Nondegenerate (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) →
        ∃ l : Fin (G.m + G.n),
          (∃ S P : ConstrSOSP.Circuit,
            f G.enc = ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P ∧
            IsSOLInstance S P) ∧
          (∀ S P : ConstrSOSP.Circuit,
            f G.enc = ConstrSOSP.encCircuit S ++ ConstrSOSP.encCircuit P →
            IsSOLInstance S P →
            ∀ z : List Bool, z.length = S.n → P.eval (S.eval z) ≠ z →
            ∃ v : Fin (G.m + G.n) → ℝ,
              IsCompletelyLabeled (G.A.map ((↑) : ℚ → ℝ))
                (G.B.map ((↑) : ℚ → ℝ)) v ∧ v ≠ 0 ∧
              z = List.zipWith Bool.xor
                (basisCode (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) v)
                (basisCode (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) 0) ∧
              ¬ ∃ w, LHOriented (G.A.map ((↑) : ℚ → ℝ))
                (G.B.map ((↑) : ℚ → ℝ)) l v w) := by sorry
