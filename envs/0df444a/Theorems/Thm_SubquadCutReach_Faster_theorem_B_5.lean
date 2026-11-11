-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_theorem_B_5
-- name    : SubquadCutReach.Faster.theorem_B_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:57:23.771723+00:00
-- url     : https://prove2.me/theorems/23816162-ba32-469c-81e2-985ac97756b2
-- title:
--   Theorem B.5 — Cut counting
-- statement:
--   There is a uniform positive integer exponent constant $C$ such that the following holds. Let $H$ have $m\le n$ vertices, minimum nontrivial cut at least $\lambda\ge0$, and let $\alpha\ge2$ be an integer. Then
--
--   $$|\{\varnothing\ne S\subsetneq V:C_H(S)<\alpha\lambda\}|\le n^{C\alpha}.$$
--
--   The constant precedes $n,H,\lambda,\alpha$. The zero-threshold case has no qualifying cut. Both shores may be counted; this affects only the unspecified exponent constant. This is the uniform cut-counting input for the reserve union bound.
--
--   Differences from the source:
--   - encoding: cuts of size less than αλ bounded by n^{O(α)} → nonempty proper shores, possibly counting both complementary shores, bounded by n^{Cα} for one positive integer C; reason: the conventional unordered-cut count differs by at most a factor two, absorbed into a uniform exponent for n≥2; empty and singleton graphs have no nontrivial shores and λ=0 has no qualifying cut
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 26, Theorem B.5 (PDF p. 28)

import Definitions.Def_SubquadCutReach_Faster_Graphs

set_option autoImplicit false
open scoped Classical

namespace SubquadCutReach.Faster

theorem theorem_B_5 :
    ∃ C : ℕ, 0 < C ∧ ∀ n m : ℕ, m ≤ n → ∀ H : SimpleGraph (Fin m),
      ∀ lam : ℝ, 0 ≤ lam →
      (∀ S : Finset (Fin m), S.Nonempty → S ≠ Finset.univ → lam ≤ (cut H S : ℝ)) →
      ∀ α : ℕ, 2 ≤ α →
        ((Finset.univ.filter fun S : Finset (Fin m) =>
          S.Nonempty ∧ S ≠ Finset.univ ∧ (cut H S : ℝ) < α*lam).card : ℝ) ≤
          (n:ℝ)^(C*α) := by sorry

end SubquadCutReach.Faster
