-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P38_inverse_sqrt_overlaps
-- name    : QAlgorithms.Papers.Independent.Extend50.P38.inverse_sqrt_overlaps
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:51:01.031028+00:00
-- url     : https://prove2.me/theorems/2cfbdd1d-cc13-4644-bfb0-5d0dd8e1f515
-- title:
--   Supported inverse-square-root overlaps in a port signal basis
-- statement:
--   Use $N\geq1$ singlet signals $\sigma_i=2^{-(N-1)}P^-_{BA_i}\otimes I_{\bar A_i}$ and $\rho=\sum_i\sigma_i$. Fix a port $i$. For the sequentially coupled basis of the other $N-1$ Alice spins, define $|\xi^{(i)}(s,m,\alpha)\rangle=|\psi^-\rangle_{BA_i}|\Phi^{[N-1]}(s,m,\alpha)\rangle_{\bar A_i}$, with all allowed spins, magnetic indices, and multiplicity paths. The inverse square root is spectral, with value zero on the kernel. With $\lambda_j^-=(N/2-j)/2^N$ and $\lambda_j^+=(N/2+j+1)/2^N$,
--
--   $$\langle\xi^{(i)}(s,m,\alpha)|\rho^{-1/2}|\xi^{(i)}(s',m',\alpha')\rangle=\delta_{s,s'}\delta_{m,m'}\delta_{\alpha,\alpha'}\left[\frac{s}{2s+1}(\lambda^-_{s-1/2})^{-1/2}+\frac{s+1}{2s+1}(\lambda^+_{s+1/2})^{-1/2}\right].$$
--
--   At $s=0$ the absent lower-spin branch has weight zero. The formula is a compression to the indicated port basis and supplies the scalar overlaps needed for fidelity and optimality. Define rhoMinus and rhoPlus by Eq.(B1), summing the eigenvalue-weighted projectors of the constructed coupled vectors in the total-spin j+1/2 and j−1/2 branches respectively. The same fixed-port overlap with rhoMinus^(-1/2) equals the Kronecker delta times the first summand above; with rhoPlus^(-1/2) it equals the delta times the second summand, as in (B3) and (B4).
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, PDF p. 3, Eqs. (4)–(5); Appendix B p.6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.

open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)

open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.3 Eqs.(4)–(5), with the separate rhoMinus/rhoPlus contributions
(B3)–(B4) in Appendix B, PDF p.6. The branch operators are the constructed
spectral sums (B1). These are fixed-port compressions, not global blocks in xi. -/
theorem inverse_sqrt_overlaps (n : ℕ) (i : Fin (n + 1))
    (p p' : SpinPath n) (m m' : ℤ)
    (hm : ValidMagnetic (finalSpin p) m) (hm' : ValidMagnetic (finalSpin p') m') :
    let s := (finalSpin p : ℝ) / 2
    (inner ℂ (xi i p m)
      (act (supportedInvSqrt (∑ j, singletSignals (n + 1) j)) (xi i p' m')) =
      if p = p' ∧ m = m' then (overlapCoefficient (n + 1) s : ℂ) else 0) ∧
    (inner ℂ (xi i p m)
      (act (supportedInvSqrt (singletSpinBranch (n + 1) false)) (xi i p' m')) =
      if p = p' ∧ m = m' then
        (((Real.sqrt (lambdaMinus (n + 1) (s - 1 / 2)))⁻¹ * s / (2 * s + 1) : ℝ) : ℂ)
      else 0) ∧
    (inner ℂ (xi i p m)
      (act (supportedInvSqrt (singletSpinBranch (n + 1) true)) (xi i p' m')) =
      if p = p' ∧ m = m' then
        (((Real.sqrt (lambdaPlus (n + 1) (s + 1 / 2)))⁻¹ * (s + 1) / (2 * s + 1) : ℝ) : ℂ)
      else 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P38

end
