-- Prove2me | Theorems.Thm_StatComplexityDM_TabularPS_hellinger_cond_le_four_joint
-- name    : StatComplexityDM.TabularPS.hellinger_cond_le_four_joint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:16.751639+00:00
-- url     : https://prove2.me/theorems/82e07264-b76d-4da9-92c1-d6c494593902
-- title:
--   Lemma A.9 — conditional squared Hellinger distance is at most four times joint distance
-- statement:
--   Let $P_{X,Y}$ and $Q_{X,Y}$ be two joint probability laws on finite alphabets $X\times Y$, with $X$-marginals $P_X,Q_X$ and conditional kernels $K_x=P_{Y\mid X=x}$, $L_x=Q_{Y\mid X=x}$. Then
--   $$
--   \sum_x P_X(x)D_H^2(K_x,L_x)\le 4D_H^2(P_{X,Y},Q_{X,Y}).
--   $$
--   This compares the conditional discrepancies used layer by layer with the discrepancy of the joint observation.
--
--   **Formalization Note** All probability laws are vectors on finite alphabets. A conditional kernel is supplied even at an $x$ to which its marginal assigns zero mass; those values do not affect the left side.
-- source:
--   arXiv:2112.13487v3, Lemma A.9, p. 71

import Mathlib
import Definitions.Def_StatComplexityDM_TabularPS_MDP

namespace StatComplexityDM.TabularPS

/-- Lemma A.9, p. 71, on finite alphabets. -/
theorem hellinger_cond_le_four_joint {X Y : Type*} [Fintype X] [Fintype Y]
    (PX QX : X → ℝ) (K L : X → Y → ℝ)
    (hPX : StatComplexityDM.LowerBound.IsDist PX) (hQX : StatComplexityDM.LowerBound.IsDist QX)
    (hK : ∀ x, StatComplexityDM.LowerBound.IsDist (K x)) (hL : ∀ x, StatComplexityDM.LowerBound.IsDist (L x)) :
    ∑ x, PX x * FoundationsRL.GeneralDM.hellingerSq (K x) (L x) ≤
      4 * FoundationsRL.GeneralDM.hellingerSq
        (fun xy : X × Y => PX xy.1 * K xy.1 xy.2)
        (fun xy : X × Y => QX xy.1 * L xy.1 xy.2) := by sorry

end StatComplexityDM.TabularPS
