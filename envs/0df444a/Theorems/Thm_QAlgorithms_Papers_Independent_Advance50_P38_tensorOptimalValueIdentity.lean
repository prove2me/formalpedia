-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P38_tensorOptimalValueIdentity
-- name    : QAlgorithms.Papers.Independent.Advance50.P38.tensorOptimalValueIdentity
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:52:32.188532+00:00
-- url     : https://prove2.me/theorems/289e3ee5-6f30-4fd2-b80c-084c913b69f2
-- title:
--   Proof of Theorem IV.1: equality of optimal values
-- statement:
--   Let $r>0$, let all dimensions $N_k>0$, and let $X$ be an arbitrary complex tensor indexed by $(i_1,\ldots,i_r)$. Use the factor order of (179), put $x=\operatorname{vec}X$, and let $y=e_1\otimes\cdots\otimes e_1$. With the inner product conjugate-linear in its first argument,
--   $$\max_{U=\bigotimes_k U_k,\,U_k\in\mathrm{SU}(N_k)}\operatorname{Re}\operatorname{tr}(xx^\dagger Uyy^\dagger U^\dagger)=\max_{\|z_k\|_2=1}|\langle X,z_1\otimes_a\cdots\otimes_a z_r\rangle|^2.$$
--   Both maxima are attained. For each $U$ the transfer equals $|\langle X,(U_1e_1)\otimes_a\cdots\otimes_a(U_re_1)\rangle|^2$. This independently displayed optimal-value identity does not assert the deferred coefficient formula of Theorem IV.1.
-- source:
--   Gradient Flows for Optimisation and Quantum Control: Foundations and Applications, arXiv:0802.4195v2, PDF p. 29, Proof of Theorem IV.1: equality of optimal values

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

/-- Equality of attained optimal values in the proof of Theorem IV.1,
PDF p.29; distinct from the deferred coefficient correspondence. -/
theorem tensorOptimalValueIdentity {r : ℕ} (hr : 0 < r) (d : Fin r → ℕ)
    (hd : ∀ k, 0 < d k) (X : ArrayIndex d → ℂ) :
    (∀ U : (k : Fin r) → Matrix.specialUnitaryGroup (Fin (d k)) ℂ,
      pureStateTransfer X (tensorSeed d) (tensorUnitary U) = Complex.normSq (vInner X
        (tensorProduct (fun k j => (U k : (Matrix (Fin (d k)) (Fin (d k)) ℂ)) j ⟨0, hd k⟩)))) ∧
    ∃ v : ℝ,
      IsGreatest {v | ∃ U : (k : Fin r) → Matrix.specialUnitaryGroup (Fin (d k)) ℂ,
        v = pureStateTransfer X (tensorSeed d) (tensorUnitary U)} v ∧
      IsGreatest {v | ∃ z : (k : Fin r) → Fin (d k) → ℂ,
        unitTensorFactors z ∧ v = Complex.normSq (vInner X (tensorProduct z))} v := by sorry

end

end QAlgorithms.Papers.Independent.Advance50.P38
