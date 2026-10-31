-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P67_spinBlocks_compressedMoments
-- name    : QAlgorithms.Papers.Independent.Intake100.P67.spinBlocks_compressedMoments
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:23:09.531906+00:00
-- url     : https://prove2.me/theorems/fdc0903a-1a4d-4001-800b-07e4e6decfbe
-- title:
--   Spin block decomposition and compressed inverse-power identity
-- statement:
--   Let $N\ge1$, let $y\in\mathbb R\setminus\{0\}$, and use the qubit signal matrices $\sigma_i$ and their sum $\rho$. For each allowed residual spin $s\le(N-1)/2$, let $R_i(s)=P^-_{A_iC}\otimes P^{\bar A_i}_s$, where the second factor projects the remaining $N-1$ Alice spins onto spin $s$. Write $\sigma_i(s)=2^{-(N-1)}R_i(s)$ and $\rho(s)=P_s^{AC}\rho$. Inverse powers vanish on the kernel. Then $\rho=\sum_s\rho(s)$, $\sigma_i=\sum_s\sigma_i(s)$, and $\rho(s)\sigma_i(t)=\sigma_i(t)\rho(s)=0$ for $s
--   e t$.
--
--   For any three allowed spins $s,t,u$,
--
--   $$R_i(s)\rho(u)^{-1/y}R_i(t)=\delta_{s,u}\delta_{t,u}\,c(s,y)R_i(s),$$
--
--   where
--
--   $$c(s,y)=\frac{s}{2s+1}(\lambda^-_{s-1/2})^{-1/y}+\frac{s+1}{2s+1}(\lambda^+_{s+1/2})^{-1/y}.$$
--
--   Here $\lambda_j^\pm$ are the eigenvalues in (7), and the first summand is omitted at $s=0$. The identity includes every magnetic and residual multiplicity matrix element of (25).
--
--   It is the scalar compression used to evaluate the SRM fidelity.
-- source:
--   Quantum teleportation scheme by selecting one of multiple output ports, arXiv:0901.2975v2, PDF p. 5, §III, Eqs. (24)–(26)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P67

noncomputable section

open scoped Matrix Kronecker ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P67

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Advance50.P49 (spinMultiplicity)

/-- PDF pp.4–5, Eqs.(24)–(26): simultaneous spin blocks and the complete compressed
moment identity. This operator form is Eq.(25) on every m,beta matrix element.
The source's reciprocal silently requires y != 0; inverse powers act on support. -/
theorem spinBlocks_compressedMoments (N : ℕ) (hN : 1 ≤ N) (y : ℝ) (hy : y ≠ 0) :
    portRho N = ∑ k ∈ spins (N - 1), rhoBlock N k ∧
    (∀ i : Fin N, portSignal N i = ∑ k ∈ spins (N - 1), signalBlock i k) ∧
    (∀ (i : Fin N) (k l : ℕ), k ∈ spins (N - 1) → l ∈ spins (N - 1) → k ≠ l →
      rhoBlock N k * signalBlock i l = 0 ∧
      signalBlock i l * rhoBlock N k = 0) ∧
    (∀ (i : Fin N) (k l m : ℕ), k ∈ spins (N - 1) → l ∈ spins (N - 1) →
      m ∈ spins (N - 1) →
      xiProjector i k * supportPower (rhoBlock N m) (-1 / y) * xiProjector i l =
        if k = m ∧ l = m then (compressedScalar N k y : ℂ) • xiProjector i k else 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P67

end
