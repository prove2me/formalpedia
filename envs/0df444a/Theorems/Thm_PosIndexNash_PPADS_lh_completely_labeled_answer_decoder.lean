-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lh_completely_labeled_answer_decoder
-- name    : PosIndexNash.PPADS.lh_completely_labeled_answer_decoder
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:45:57.045386+00:00
-- url     : https://prove2.me/theorems/22cb635f-0c0f-44b7-be3f-9139ea529deb
-- title:
--   Theorem 3.2, answer step — exact rational decoding of a non-artificial completely labeled basis
-- statement:
--   Fix a nondegenerate rational bimatrix game $G=(A,B)$ with $m,n\ge1$ and strictly positive payoffs. If $v=(\widetilde x,\widetilde y)\ne0$ is a completely labeled vertex of the product best-response polytope and $z=\chi(v)\operatorname{xor}\chi(0)$ is its canonical basis code, then the equilibrium from eq. (7),
--   $$
--   x=\frac{\widetilde x}{\mathbf1^\top\widetilde x},\qquad
--   y=\frac{\widetilde y}{\mathbf1^\top\widetilde y},
--   $$
--   has exact rational coordinates and can be recovered from $\langle G\rangle$ and $z$ in polynomial time.
--
--   Thus there is a polynomial-time decoder $g$ whose output is the prescribed binary code of rational vectors $x,y$, whose real casts agree with these normalized strategies, and which form a Nash equilibrium. Nondegeneracy makes this equilibrium regular, so its Shapley index is nonzero and therefore lies in $\{-1,+1\}$. This isolates exact support-system solving and binary rational output formatting from the orientation argument.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF), p. 15, eq. (7); p. 19, Theorem 3.2 answer decoding and support systems (4); p. 12, Definitions 2.2–2.3

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_PosIndexNash_PPADS_PositivePayoffNash
import Definitions.Def_PosIndexNash_PPADS_LemkeHowson

theorem PosIndexNash.PPADS.lh_completely_labeled_answer_decoder :
    ∃ g : List (Option (Bool ⊕ Bool)) → List Bool,
      CookPvsNP.PolyTimeComputable g ∧
      ∀ G : QuasiStrictNE.RatGame, 1 ≤ G.m → 1 ≤ G.n →
        (∀ i j, 0 < G.A i j) → (∀ i j, 0 < G.B i j) →
        Nondegenerate (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) →
        ∀ (z : List Bool) (v : Fin (G.m + G.n) → ℝ),
          IsCompletelyLabeled (G.A.map ((↑) : ℚ → ℝ))
            (G.B.map ((↑) : ℚ → ℝ)) v → v ≠ 0 →
          z = List.zipWith Bool.xor
            (basisCode (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) v)
            (basisCode (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ)) 0) →
          ∃ (x : Fin G.m → ℚ) (y : Fin G.n → ℚ),
            g (G.enc.map (some ∘ Sum.inl) ++ none :: z.map (some ∘ Sum.inr)) =
              CardinalMatching.encRatVec G.m x ++ CardinalMatching.encRatVec G.n y ∧
            (fun i => (x i : ℝ)) = lhRowStrategy v ∧
            (fun j => (y j : ℝ)) = lhColStrategy v ∧
            QuasiStrictNE.IsNE (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
              (fun i => (x i : ℝ)) (fun j => (y j : ℝ)) ∧
            (shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
                (fun i => (x i : ℝ)) (fun j => (y j : ℝ)) = -1 ∨
              shapleyIndex (G.A.map ((↑) : ℚ → ℝ)) (G.B.map ((↑) : ℚ → ℝ))
                (fun i => (x i : ℝ)) (fun j => (y j : ℝ)) = 1) := by sorry
