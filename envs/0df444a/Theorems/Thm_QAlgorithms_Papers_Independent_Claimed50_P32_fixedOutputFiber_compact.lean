-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P32_fixedOutputFiber_compact
-- name    : QAlgorithms.Papers.Independent.Claimed50.P32.fixedOutputFiber_compact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:27:15.11386+00:00
-- url     : https://prove2.me/theorems/6592bbe8-8ab3-401d-bdf3-d767611dd6e9
-- title:
--   Operations with a fixed faithful-state output form a compact fiber
-- statement:
--   Let $\sigma$ be a faithful input state on a nonzero separable complex Hilbert space, and let $A$ be any positive trace-class output operator with $\operatorname{Tr}A\leq1$. Then
--
--   $$\{\Phi\in\mathfrak F_{\leq1}:\Phi(\sigma)=A\}\text{ is strongly compact}.$$
--
--   The conclusion includes $A=0$ and finite-dimensional spaces. It is the fixed-output compactness application in Example 1.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, PDF p. 9, §3, Example 1: compact fixed-output operation fiber

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32

noncomputable section

open Filter

open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

open QAlgorithms.RealRegisters (Hilbert)

/-- §3, Example 1, PDF pp.9--10: the fixed-output operation fiber is strongly
compact. This includes A=0 and finite-dimensional input/output spaces. -/
theorem fixedOutputFiber_compact {I J : Type}
    [Countable I] [Nonempty I] [Countable J] [Nonempty J] (sigma : Nuclear.State I)
    (hfaithful : Operators.HasFullSupport sigma) (A : TraceSubstate J) :
    IsCompact {Phi : CanonicalOperation I J | evaluate Phi sigma = A.val} := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P32

end
