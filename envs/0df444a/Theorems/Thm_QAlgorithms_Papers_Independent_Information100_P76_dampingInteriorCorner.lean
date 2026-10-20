-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P76_dampingInteriorCorner
-- name    : QAlgorithms.Papers.Independent.Information100.P76.dampingInteriorCorner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:02:52.519985+00:00
-- url     : https://prove2.me/theorems/20bfa90a-1334-4e20-b316-e9fd16fcf543
-- title:
--   Proposition 7.5: a generalized amplitude-damping channel with an interior corner
-- statement:
--   For $0\le\nu,p\le1$, define the qubit channel $\Phi_{\nu,p}(X)=\sum_{a=0}^3K_aXK_a^*$ by
--
--   $$K_0=\sqrt p\operatorname{diag}(1,\sqrt{1-\nu}),\quad K_1=\sqrt{p\nu}|0\rangle\langle1|,\quad K_2=\sqrt{1-p}\operatorname{diag}(\sqrt{1-\nu},1),\quad K_3=\sqrt{(1-p)\nu}|1\rangle\langle0|.$$
--
--   These Kraus operators satisfy $\sum_a K_a^*K_a=I$. At $\nu=1/2$ and $p=3/4$, writing $H_2$ for binary entropy in bits and $h$ for maximum entropy exchange,
--
--   $$0<H_2(7/12)-H_2(1/3)\le\kappa\le1-H_2(3/4)<H_2(3/8)\le h.$$
--
--   In particular, $0.061572\le\kappa\le0.188722$, $h\ge0.954434$, and $0<\kappa<h$. The displayed decimals are rounded in the directions preserving their inequalities. This gives an interior resource corner without asserting the exact value of $\kappa$ or any numerical optimizer.
-- source:
--   Bath dimension and initial entropy for closed repeated use of a quantum channel, arXiv:2609.18267v1, PDF p. 13, Proposition 7.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P76

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open Filter

/-- PDF pp.13–14, Proposition 7.5: analytic bracket and inward-rounded decimals.
No numerical search is made into an optimizer or an exact value of kappa. -/
theorem dampingInteriorCorner :
    (∀ nu p : ℝ, 0 ≤ nu → nu ≤ 1 → 0 ≤ p → p ≤ 1 →
      IsKrausFamily (generalizedDampingKraus nu p)) ∧
    (let Phi := dampingChannel (1 / 2) (3 / 4)
     0 < binEntropy2 (7 / 12) - binEntropy2 (1 / 3) ∧
     binEntropy2 (7 / 12) - binEntropy2 (1 / 3) ≤ intrinsicCost Phi ∧
     intrinsicCost Phi ≤ 1 - binEntropy2 (3 / 4) ∧
     1 - binEntropy2 (3 / 4) < binEntropy2 (3 / 8) ∧
     binEntropy2 (3 / 8) ≤ exchangeCost Phi ∧
     (0.061572 : ℝ) ≤ intrinsicCost Phi ∧ intrinsicCost Phi ≤ (0.188722 : ℝ) ∧
     (0.954434 : ℝ) ≤ exchangeCost Phi ∧
     0 < intrinsicCost Phi ∧ intrinsicCost Phi < exchangeCost Phi) := by sorry

end QAlgorithms.Papers.Independent.Information100.P76

end
