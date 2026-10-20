-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_classical_specializations
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.classical_specializations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:05:34.012807+00:00
-- url     : https://prove2.me/theorems/47ab9617-9bee-45f7-9182-a37cab21f02a
-- title:
--   Empty-side-information and Arimoto specializations
-- statement:
--   Fix $\alpha\in[1/2,1)\cup(1,\infty)$ and a probability distribution $p$ on a finite set $Y$. For any normalized PSD states $\rho_A^y$ and $\rho_{AY}=\bigoplus_y p_y\rho_A^y$,
--
--   $$
--   \widetilde H_\alpha(A|Y)_\rho=\frac{\alpha}{1-\alpha}\log_2\sum_y p_y\,2^{\frac{1-\alpha}{\alpha}H_\alpha(\rho_A^y)}.
--   $$
--
--   Independently, for any conditional distributions $r_{x|y}$ on a finite set $X$ and the diagonal joint state with probabilities $p_y r_{x|y}$,
--
--   $$
--   \widetilde H_\alpha(X|Y)=\frac{\alpha}{1-\alpha}\log_2\sum_y p_y\left(\sum_x r_{x|y}^\alpha\right)^{1/\alpha}.
--   $$
--
--   These are both explicit specializations of Proposition 9, the second identified by the source with Arimoto's classical conditional entropy.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 12, Empty-side-information and Arimoto specializations

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF pp.12–13: both empty-quantum-side-information and Arimoto specializations.
The order reading is inherited from the measurement step in Proposition 9's proof. -/
theorem classical_specializations {A X Y : Type} [Fintype A] [Fintype X] [Fintype Y]
    [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (a : ℝ) (ha : (1/2 : ℝ) ≤ a ∧ a ≠ 1) (p : Distribution Y)
    :
    (∀ rho : Y → Mat A, (∀ y, Density (rho y)) →
      conditionalRenyi a (cq p.val rho) =
        (a / (1-a) * Real.logb 2 (∑ y, p.val y * (2 : ℝ) ^ (((1-a)/a) * renyiEntropy a (rho y))) : ℝ)) ∧
    (∀ r : Y → Distribution X,
      conditionalRenyi a (cq p.val (fun y => Matrix.diagonal (fun x => ((r y).val x : ℂ)))) =
        (a / (1-a) * Real.logb 2 (∑ y, p.val y * (∑ x, (r y).val x ^ a) ^ (1/a)) : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
