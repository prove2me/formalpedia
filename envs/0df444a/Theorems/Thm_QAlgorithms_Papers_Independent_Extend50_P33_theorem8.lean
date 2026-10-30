-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_theorem8
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.theorem8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:46:11.929624+00:00
-- url     : https://prove2.me/theorems/af790134-f667-42be-a999-1f9afe690225
-- title:
--   Theorem 8 (summary Theorem 4): jointly optimal probabilistic PBT resource and measurements
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Put $g=(\sum_{\nu\vdash N}m_\nu^2)^{-1}$, $X=\sum_\mu d^Ngm_\mu P_\mu/d_\mu$, $O=\sqrt X$, and $\zeta=(O\otimes I)\Phi_d^{\otimes N}$ with normalized Bell pairs. Set $\Theta_a=\sum_\alpha d^{N+1}g m_\alpha P_{\alpha,\bar a}/(N d_\alpha)$. These matrices are feasible for the joint exact-success SDP. The matrix $O$ is positive and invertible, $\zeta$ has norm one, and conjugating the transformed effects $Q_{an}\otimes\Theta_a$ by $O^{-1}\otimes I$ and adjoining their residual failure effect gives a physical POVM. The attained global maximum is
--
--   $$p_{\rm opt}=\frac{N}{N+d^2-1}.$$
--
--   This specifies both the optimal resource and measurement, with the failure outcome included.
--
--   Optimality also ranges over all physical perfect-conclusive POVMs. For each conclusive outcome the channel obtained by measuring Alice and discarding every Bob port except the selected one equals a nonnegative scalar times the identity on every input operator; the scalars sum to the displayed success probability. In the joint optimization every normalized pure resource on the stated Alice and Bob registers is allowed, including singular filters.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 12, Theorem 8 (summary Theorem 4): jointly optimal probabilistic PBT resource and measurements

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

/-- PDF p.12 Theorem8 (summary Theorem4 p.4): actual resource, physical
POVM and attained joint optimum. SDP effects are conjugated by O^(-1).
The Bell vector in the resource is normalized. Perfect teleportation and
optimality range over the actual physical resource/POVM protocols. -/
theorem theorem8 (d k : ℕ) (hd : 2 ≤ d) :
    JointFeasible (jointX d k) (jointTheta d k) ∧
    IsGreatest (jointValues d k) (optimalProbability d (k+2)) ∧
    pbtSuccessProbability (jointTheta d k) = optimalProbability d (k+2) ∧
    (jointO d k).PosSemidef ∧ jointO d k * jointO d k = jointX d k ∧
    IsUnit (jointO d k) ∧ IsState (resourceVector d k) ∧
    (∀ a, (jointPhysical d k a).PosSemidef) ∧ (jointFailure d k).PosSemidef ∧
    jointFailure d k + ∑ a, jointPhysical d k a = 1 ∧
    ExactPBT (jointO d k) (jointPhysical d k) (optimalProbability d (k+2)) ∧
    IsGreatest (jointOperationalValues d k) (optimalProbability d (k+2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
