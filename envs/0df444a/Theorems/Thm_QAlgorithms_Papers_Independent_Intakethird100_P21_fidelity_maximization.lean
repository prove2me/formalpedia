-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P21_fidelity_maximization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P21.fidelity_maximization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:56:27.377193+00:00
-- url     : https://prove2.me/theorems/4147a9da-88dc-47d3-bccb-4eb249a2f1d8
-- title:
--   Pure-state fidelity bound with the support-qualified equality case
-- statement:
--   Let $d\ge2$, let $\mu_1,\ldots,\mu_d\ge0$ sum to one, and let $U_A,U_B$ be local unitaries. Put $V=U_A^T U_B$, $\Phi_d=d^{-1/2}\sum_k|k,k\rangle$, and $\psi=(U_A\otimes U_B)\sum_k\sqrt{\mu_k}|k,k\rangle$. The squared overlap satisfies
--
--   $$
--   \langle\Phi_d|\psi\rangle\langle\psi|\Phi_d\rangle
--   =F(\mu,V):=\frac1d\left|\sum_k\sqrt{\mu_k}V_{kk}\right|^2
--   \le F(\mu,I).
--   $$
--
--   Equality holds exactly when there exists a common complex phase $z$, $|z|=1$, such that $V_{kk}=z$ for every $k$ with $\mu_k>0$. With full Schmidt support this is equivalent to $V=zI$.
--
--   This supplies the fidelity maximization used in the scalar reduction. The product order and support qualifier correct the printed prose; the inequality retains zero Schmidt probabilities.
-- source:
--   I-concurrence and tangle for isotropic states, arXiv:quant-ph/0208002v1, PDF p. 6, §3.1, (3.6)–(3.7): pure-state fidelity bound and its equality condition

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P21

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P03
  (PureEnsemble convexRoof pureConcurrence concurrence SchmidtData schmidtVector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, (3.6)--(3.7), corrected: V=UA-transpose times UB.
Printed unrestricted equality iff V is scalar fails for zero Schmidt probabilities;
the common phase is required exactly on their positive support. -/
theorem fidelity_maximization (d : ℕ) (hd : 2 ≤ d) (mu : SchmidtProbabilities d)
    (UA UB : Matrix.unitaryGroup (Fin d) ℂ) :
    let V := (UA : Matrix (Fin d) (Fin d) ℂ)ᵀ * (UB : Matrix (Fin d) (Fin d) ℂ)
    maximallyEntangledOverlap (pureDensity (act (Matrix.kronecker (UA : Matrix (Fin d) (Fin d) ℂ)
      (UB : Matrix (Fin d) (Fin d) ℂ)) (canonicalVector mu))) = fidelityProfile mu V ∧
    fidelityProfile mu V ≤ fidelityProfile mu 1 ∧
    (fidelityProfile mu V = fidelityProfile mu 1 ↔
      ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ k, 0 < mu.probability k → V k k = z) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P21

end
