-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_lemma35
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.lemma35
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:59:18.467797+00:00
-- url     : https://prove2.me/theorems/4962b819-4121-4c94-a0bf-f6d939db15d1
-- title:
--   Lemma 35: square-root specialization and EPR-resource fidelity
-- statement:
--   Use $N\ge1$, $d\ge2$, physical diagrams $\alpha\vdash N-1$, $\mu\vdash N$, and one-box compatibility $\mu\in\alpha$. Let $d_\lambda$ and $m_\lambda$ be the actual Specht dimensions and tensor-permutation multiplicities. The operators $F_\mu(\alpha)$ are constructed by Eq. (145), and $\lambda_\mu(\alpha)=N m_\mu d_\alpha/(d^N m_\alpha d_\mu)>0$. All sums below use compatible physical labels. Write $\rho_\alpha^t=\sum_{\mu\in\alpha}\lambda_\mu(\alpha)^tF_\mu(\alpha)$, extended by zero off its support.
--
--   Set $z_\alpha=1$ and $y_\alpha=2$. The block effects become the global square-root effects $E_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$, where $\rho=\sum_a\sigma_a$ and the inverse is zero on the kernel. Their positive residual completion is a deterministic POVM, has the same fidelity, and is optimal for the maximally entangled resource. Explicitly,
--
--   $$F_{\mathrm{EPR}}(N,d)=\frac1{d^{N+2}}\sum_\alpha\left(\sum_{\mu\in\alpha}\sqrt{d_\mu m_\mu}\right)^2.$$
--
--   Every physical identity-summing measurement with that resource has fidelity at most this value. This recovers the expression credited to [12].
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 26, Lemma 35: square-root specialization and EPR-resource fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Lemma 35, including the displayed fixed-resource formula (120), the actual
square-root effects, their kernel completion, and fixed-resource optimality
(PDF p.26). The statement's Eq.(109) reference means Eq.(110). -/
theorem lemma35 {d K : ℕ} (hd : 2 ≤ d) :
    powerEffects (d := d) (K := K) (fun _ => 1) (fun _ => 2) = squareRootEffects d K ∧
    QAlgorithms.IsPOVM (completedMeasurement
      (1 : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ) (squareRootEffects d K)) ∧
    effectFidelity (squareRootEffects d K) = eprFormula d K ∧
    effectFidelity (completedMeasurement
      (1 : Matrix (AliceIndex d (K+1)) (AliceIndex d (K+1)) ℂ) (squareRootEffects d K)) = eprFormula d K ∧
    (∀ M : Fin (K+1) → Matrix (SignalIndex d K) (SignalIndex d K) ℂ,
      QAlgorithms.IsPOVM M → effectFidelity M ≤ eprFormula d K) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
