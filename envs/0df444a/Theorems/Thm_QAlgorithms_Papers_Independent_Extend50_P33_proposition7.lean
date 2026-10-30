-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_proposition7
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.proposition7
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:52:08.7704+00:00
-- url     : https://prove2.me/theorems/8efffde3-7510-4ddd-875f-785e98ca39b5
-- title:
--   Proposition 7: explicit optimal fixed-resource measurement
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. For every port put $\Theta_a=d\sum_\alpha P_{\alpha,\bar a}\min_{\mu\in\alpha}\gamma_\mu(\alpha)^{-1}$. The effects $Q_{an}\otimes\Theta_a$, together with the residual failure effect, form a feasible physical measurement attaining the fixed-resource maximum:
--
--   $$p(\Theta)=\max p=p_{\rm ME}.$$
--
--   The auxiliary $\Theta_a$ acts on the other $N-1$ ports and is not itself a complete POVM.
--
--   Optimality also ranges over all physical perfect-conclusive POVMs. For each conclusive outcome the channel obtained by measuring Alice and discarding every Bob port except the selected one equals a nonnegative scalar times the identity on every input operator; the scalars sum to the displayed success probability. In the joint optimization every normalized pure resource on the stated Alice and Bob registers is allowed, including singular filters.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 12, Proposition 7: explicit optimal fixed-resource measurement

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

/-- PDF p.12 Proposition7: the auxiliary Theta's give success effects Q⊗Theta;
the residual identity is the failure outcome. Perfect teleportation and
optimality are asserted for the actual channel on every input. -/
theorem proposition7 (d k : ℕ) (hd : 2 ≤ d) :
    FixedFeasible (fixedTheta d k) ∧
    IsGreatest (fixedValues d k) (pbtSuccessProbability (fixedTheta d k)) ∧
    pbtSuccessProbability (fixedTheta d k) = fixedRatioValue d k ∧
    ExactPBT (1 : Op d (k+2)) (fun a => effect a (fixedTheta d k a))
      (fixedRatioValue d k) ∧
    IsGreatest (fixedOperationalValues d k) (fixedRatioValue d k) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
