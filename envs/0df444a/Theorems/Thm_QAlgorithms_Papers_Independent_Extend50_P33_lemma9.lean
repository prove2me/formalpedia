-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_lemma9
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.lemma9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:53:07.266022+00:00
-- url     : https://prove2.me/theorems/166b8849-1cc9-41dd-87d0-4d796824195a
-- title:
--   Lemma 9: achievable jointly optimized primal value
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Let $g$, $X$ and $\Theta_a$ be the explicit matrices of Eqs.(108)–(109), equivalently those specified in Theorem 8. They obey $X\succeq0$, $\operatorname{Tr}X=d^N$, $\Theta_a\succeq0$, and $\sum_aQ_{an}\otimes\Theta_a\preceq X\otimes I$. Their attained objective is
--
--   $$\frac1{d^{N+1}}\sum_a\operatorname{Tr}\Theta_a=\frac{N}{N+d^2-1}.$$
--
--   This is feasibility of the constructed matrices and does not assert equality on the complementary zero ideal.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 12, Lemma 9: achievable jointly optimized primal value

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.

local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- PDF pp.12,28–29 Lemma9: feasibility of the actual Eqs.(108)–(109)
matrices and their evaluated objective, without claiming saturation on the kernel. -/
theorem lemma9 (d k : ℕ) (hd : 2 ≤ d) :
    JointFeasible (jointX d k) (jointTheta d k) ∧
    pbtSuccessProbability (jointTheta d k) = optimalProbability d (k+2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
