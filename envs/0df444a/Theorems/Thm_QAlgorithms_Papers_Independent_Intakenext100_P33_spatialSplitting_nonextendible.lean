-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P33_spatialSplitting_nonextendible
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P33.spatialSplitting_nonextendible
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:09:08.520632+00:00
-- url     : https://prove2.me/theorems/57ab7065-a9fc-4d71-bbae-946ca7d50627
-- title:
--   Passive spatial splitting reduces amplitudes and prevents fixed-amplitude extension
-- statement:
--   Let $B$ be a unitary two-port optical splitter. For any coherent input amplitude $z\in\mathbb C$ and vacuum at the unused input,
--
--   $$
--   U_B\bigl(|z\rangle\otimes|0\rangle\bigr)=|B_{00}z\rangle\otimes|B_{10}z\rangle.
--   $$
--
--   For every $N\ge1$, construct the lossless equal $N$-port splitter as the Fourier unitary with first column $1/\sqrt N$. Its action on an $m$-photon first-port input is the normalized occupation expansion of $(\sum_j a_j^\dagger/\sqrt N)^m/\sqrt{m!}$, with its full-Fock coefficient realization. The coherent number expansion is summable and its image is $|z/\sqrt N\rangle^{\otimes N}$. Thus a uniformly phase-averaged fixed input amplitude $\alpha\ge0$ produces a normalized spatial density
--
--   $$
--   \sigma_N(\alpha)=\rho_N(\alpha/\sqrt N).
--   $$
--
--   For $\alpha>0$,
--
--   $$
--   \operatorname{tr}_{N+1}\sigma_{N+1}(\alpha)\ne\sigma_N(\alpha).
--   $$
--
--   Port phases are fixed by the chosen first column. Increasing the number of equally illuminated spatial modes changes the amplitudes of the original modes. This distinguishes fixed-total-energy spatial splitting from the compatible temporal family; no no-cloning conclusion is asserted.
-- source:
--   The Quantum State of a Propagating Laser Field, arXiv:quant-ph/0111157v1, PDF p. 5, IIE, Eq.(25)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P33

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P33

open Filter MeasureTheory

open scoped Topology Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P39

-- Accepted scalar phase; positive exponential, differing only by commuting scalars.

open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- arXiv:quant-ph/0111157v1, PDF p.5, Eq.(25) and §IIE.
A unitary two-port splitter gives coherent outputs, and a constructed passive
equal N-port splitter gives the fixed-total-energy spatial family. With a
nonzero input its N+1 extension changes the original N modes. N=0 is excluded;
this is energy sharing rather than a claim of cloning. -/
theorem spatialSplitting_nonextendible :
    (∀ (B : Matrix (Fin 2) (Fin 2) ℂ), B ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      ∀ z : ℂ,
        QAlgorithms.Papers.Independent.Frontier18.P14.passiveApply B
          (QAlgorithms.Papers.Independent.Frontier18.P14.coherentPair z 0) =
        QAlgorithms.Papers.Independent.Frontier18.P14.coherentPair (B 0 0 * z) (B 1 0 * z)) ∧
    (∀ N : ℕ, 1 ≤ N →
      equalSplitter N ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
      (∀ m, Memℓp (splitNumberCoefficients N m) 2 ∧
        (∀ q, splitNumber N m q = splitNumberCoefficients N m q) ∧ ‖splitNumber N m‖ = 1) ∧
      (∀ z : ℂ, Summable (fun m : ℕ => coherentCoefficient z m • splitNumber N m) ∧
        splitCoherent N z = packetCoherent (fun _ : Fin N => z / (Real.sqrt (N : ℝ) : ℂ))) ∧
      (∀ alpha : ℝ, 0 ≤ alpha →
        spatialBeam alpha N = commonPhase (alpha / Real.sqrt (N : ℝ)) N ∧
        IsPacketDensity (spatialBeam alpha N) ∧
        (0 < alpha → discardLastPacket (spatialBeam alpha (N + 1)) ≠ spatialBeam alpha N))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P33

end
