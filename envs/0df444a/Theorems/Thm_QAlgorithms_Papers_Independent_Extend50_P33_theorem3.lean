-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_theorem3
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.theorem3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:48:18.984261+00:00
-- url     : https://prove2.me/theorems/663506f9-368b-4795-9070-590dde26ba29
-- title:
--   Theorem 3: optimal probabilistic PBT with maximally entangled resource
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. The maximum is attained over all exact-success probabilistic PBT measurements with the maximally entangled resource, and equals
--
--   $$p_{\rm ME}=\frac1{d^N}\sum_{\alpha\vdash N-1}m_\alpha^2\min_{\mu\in\alpha}\frac{d_\mu}{m_\mu}.$$
--
--   The resource is fixed; only the measurement is optimized.
--
--   Optimality also ranges over all physical perfect-conclusive POVMs. For each conclusive outcome the channel obtained by measuring Alice and discarding every Bob port except the selected one equals a nonnegative scalar times the identity on every input operator; the scalars sum to the displayed success probability. In the joint optimization every normalized pure resource on the stated Alice and Bob registers is allowed, including singular filters.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 11, Theorem 3: optimal probabilistic PBT with maximally entangled resource

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

/-- PDF pp.4,11 Theorem3: attained maximum both in the source SDP and
over every physical perfect-conclusive POVM for the fixed Bell resource. -/
theorem theorem3 (d k : ℕ) (hd : 2 ≤ d) :
    IsGreatest (fixedValues d k) (fixedRatioValue d k) ∧
    IsGreatest (fixedOperationalValues d k) (fixedRatioValue d k) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
