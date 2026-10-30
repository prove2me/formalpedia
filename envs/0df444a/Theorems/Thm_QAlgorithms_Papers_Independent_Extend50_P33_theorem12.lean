-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P33_theorem12
-- name    : QAlgorithms.Papers.Independent.Extend50.P33.theorem12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:56:05.707888+00:00
-- url     : https://prove2.me/theorems/6fa01264-2357-4df7-8304-7db4259e760b
-- title:
--   Theorem 12: deterministic square-root-measurement entanglement fidelity
-- statement:
--   Let $d\ge2$ be the local dimension, $N\ge2$ the number of ports, and $n=N+1$. All physical diagrams have height at most $d$. Write $m_\lambda$ for its multiplicity in the natural tensor permutation action, $d_\lambda$ for its Specht dimension, and $P_\lambda$ for the full isotypic projector. The relation $\mu\in\alpha$ means adding one box. Let $\rho_a=B_{an}/d^N$, $\rho=\sum_a\rho_a$ and $R=\rho^{-1/2}$ with zero inverse on the kernel. Complete the square-root effects by $\Pi_a=R\rho_aR+(I-\sum_bR\rho_bR)/N$. They form a POVM, and their entanglement fidelity, $F=d^{-2}\sum_a\operatorname{Tr}(\rho_a\Pi_a)$, is
--
--   $$F=\frac1{d^{N+2}}\sum_{\alpha\vdash N-1}\left(\sum_{\mu\in\alpha}\sqrt{d_\mu m_\mu}\right)^2.$$
--
--   This evaluates the specified measurement. It makes no general measurement-optimality claim.
--
--   Here fidelity is the normalized Bell-reference entanglement fidelity of the actual channel obtained by measuring the stated POVM, selecting Bob’s port and tracing all other systems. The theorem also asserts that this constructed map is a quantum channel.
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, PDF p. 13, Theorem 12: deterministic square-root-measurement entanglement fidelity

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

/-- PDF pp.5,13–14 Theorem12: fidelity of the completed square-root
measurement, using its actual channel and normalized Bell overlap.
The square is inside the alpha sum; no optimality is asserted. -/
theorem theorem12 (d k : ℕ) (hd : 2 ≤ d) :
    (∀ a, (srm d k a).PosSemidef) ∧ (∑ a, srm d k a) = 1 ∧
    IsChannel (pbtDeterministicChannel d k) ∧
    deterministicFidelity d k (by omega) = (1/(d:ℝ)^(k+4)) *
      ∑ a : Schur.Partition d (k+1),
        (∑ b : Schur.Partition d (k+2), if Extends a b then
          Real.sqrt ((sdim b:ℝ) * mult b) else 0)^2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P33

end
