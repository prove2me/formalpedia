-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P62_photon_number_xor_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P62.photon_number_xor_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:07:29.280004+00:00
-- url     : https://prove2.me/theorems/56077f99-fdab-4903-b5d1-abc4dac06b17
-- title:
--   Two-copy photon-number and specified XOR branches coincide up to local unitary
-- statement:
--   The two parties each hold one complete oscillator mode, with joint Hilbert space $\ell^2(\mathbb N\times\mathbb N)$ and no occupation cutoff. A density means a positive trace-class operator of trace one. We use $[X_j,P_k]=i\delta_{jk}$ and vacuum covariance $I$.
--
--   Let $\rho$ be any density and $N\ge0$ an integer. Form two independent copies, grouped as $(A_1,A_2):(B_1,B_2)$. Let $X_N$ be their unnormalized branch when each party's total occupation is exactly $N$. Let $Y_N$ be the unnormalized branch obtained by first projecting each local oscillator to $\operatorname{span}\{|0\rangle,\ldots,|N\rangle\}$, then applying on both sides
--
--   $$
--   \mathrm{XOR}_{N+1}|k,\ell\rangle=|k,(\ell+k)\bmod(N+1)\rangle,
--   $$
--
--   and selecting target outcome exactly $N$ on both sides, keeping the targets. There is a full local unitary $U_N$ extending $|k,N-k\rangle\mapsto|k,N\rangle$ for $0\le k\le N$ such that
--
--   $$
--   (U_N\otimes U_N)X_N(U_N\otimes U_N)^*=Y_N,
--   \qquad \operatorname{tr}X_N=\operatorname{tr}Y_N.
--   $$
--
--   Whenever this trace $p_N$ is positive, $X_N/p_N$ and $Y_N/p_N$ are normalized densities related by the same local unitary. This is an exact algebraic branch identification, with no Gaussianity or fidelity-improvement hypothesis. At $N=0$ the identification still holds but gives no nontrivial entangled target.
-- source:
--   All inseparable two-mode Gaussian continuous variable states are distillable, arXiv:quant-ph/0007061v2, PDF p. 4, Two-copy total-number measurement equals finite truncation and XOR branch up to local relabeling

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P62

noncomputable section

open scoped BigOperators ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P62

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex GaussianWithCovariance standardFormCovariance
   multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (conjugateKernel partialRight boundedUnitaryConjugation)

open QAlgorithms.Papers.Independent.Bridge50.P18
  (HasCoefficients realizeCoefficients)

open QAlgorithms.Papers.Independent.Support50.P39 (noisyResourceCopies)

/-- arXiv:quant-ph/0007061v2, PDF p.4: exact equality of the two selected
branches after the local isometry |k,N-k> -> |k,N>, extended to a full unitary.
The equality also holds unnormalized and preserves success probability. Only
positive-probability branches are normalized. N=0 is allowed and distills no entanglement. -/
theorem photon_number_xor_equivalence
    (rho : State (ℕ × ℕ)) (N : ℕ) :
    ∃ U : Hilbert (ℕ × ℕ) ≃ₗᵢ[ℂ] Hilbert (ℕ × ℕ),
      (∀ k : ℕ, k ≤ N → U (lp.single 2 (k,N-k) 1) = lp.single 2 (k,N) 1) ∧
      bilocalConjugation U U (numberBranch N rho.coefficients) = xorBranch N rho.coefficients ∧
      branchTrace (numberBranch N rho.coefficients) = branchTrace (xorBranch N rho.coefficients) ∧
      (0 < branchTrace (numberBranch N rho.coefficients) →
        IsDensity (normalizeBranch (numberBranch N rho.coefficients)) ∧
        IsDensity (normalizeBranch (xorBranch N rho.coefficients)) ∧
        bilocalConjugation U U (normalizeBranch (numberBranch N rho.coefficients)) =
          normalizeBranch (xorBranch N rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P62

end
