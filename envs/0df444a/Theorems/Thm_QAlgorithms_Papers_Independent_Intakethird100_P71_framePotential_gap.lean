-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_framePotential_gap
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.framePotential_gap
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:05:36.539906+00:00
-- url     : https://prove2.me/theorems/39d7ae31-7ce5-4562-8886-b5b0d8d8a2e1
-- title:
--   Local frame-potential inequality and exact gap identity
-- statement:
--   Let $\nu$ be the prior of any projective experiment on $N$ qudits, $d\ge2$, and let $\nu^{\rm LS}$ be its conjugation twirl by normalized local Haar measure. Define $M_2(\nu)=\mathbb E_\nu S^{\otimes2}$ and $F_2(\nu)=\mathbb E_{S,S'\sim\nu}[\operatorname{Tr}(SS')]^2$, with independent snapshots. If $W_A$ is the second EF and $\mathrm{Wg}_{A,B}=(d^2-1)^{-N}(-1/d)^{|A\triangle B|}$, then
--
--   $$F_2(\nu)\ge F_2(\nu^{\rm LS})=\sum_{A,B}W_A\mathrm{Wg}_{A,B}W_B,$$
--
--   $$\Delta_2=F_2(\nu)-F_2(\nu^{\rm LS})=\operatorname{Tr}\bigl[(M_2(\nu)-M_2(\nu^{\rm LS}))^2\bigr].$$
--
--   Thus $\Delta_2=0$ exactly when these second moments agree, and local invariance of the whole prior law implies zero gap. At zero gap, inversion of the complete twirled measurement channel reconstructs every density matrix without bias from the original posterior. The twirled moment averages jointly over the local unitary and the snapshot. Equality of second moments does not assert equality of the full laws.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 12, §III D, Eqs.(42)–(45): local frame-potential inequality and gap identity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P71

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.Elementwise

namespace QAlgorithms.Papers.Independent.Intakethird100.P71

attribute [local instance] Classical.propDecidable

local notation "Config" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Config (P := Fin n) (fun _ => d)

local notation "Op" n:max d:max =>
  QAlgorithms.Papers.Independent.Information100.P21.Op (Config n d)

attribute [local instance] QAlgorithms.Papers.Independent.Intakethird100.P71.matrixContinuousENorm

local notation "Unitary" n:max d:max => Matrix.unitaryGroup (Config n d) ℂ

local notation "Local" n:max d:max => Fin n → Matrix.unitaryGroup (Fin d) ℂ

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.12 Eqs.(42)–(45): frame-potential inequality, EF value of the
locally twirled limit, and the trace of the square gap identity. The second
moment in the difference averages over BOTH V and the snapshot. Zero gap
ensures exact reconstruction when the twirled channel is complete; it does not
imply invariance of the entire probability law. -/
theorem framePotential_gap {n d : ℕ} (hd : 2 ≤ d) (E : ProjectiveEnsemble n d)
    (H : Measure (Local n d)) [IsProbabilityMeasure H] [H.IsMulLeftInvariant] :
    framePotential (twirled H (prior E)) ≤ framePotential (prior E) ∧
    framePotential (twirled H (prior E)) =
      ∑ A : Finset (Fin n), ∑ B : Finset (Fin n),
        feature (prior E) A * regionalWg n d A B * feature (prior E) B ∧
    (frameGap H (prior E) : ℂ) =
      ((snapshotMoment (prior E) 2 - snapshotMoment (twirled H (prior E)) 2) *
        (snapshotMoment (prior E) 2 - snapshotMoment (twirled H (prior E)) 2)).trace ∧
    (frameGap H (prior E) = 0 ↔ snapshotMoment (prior E) 2 = snapshotMoment (twirled H (prior E)) 2) ∧
    (LocallyScrambled (prior E) → frameGap H (prior E) = 0) ∧
    (frameGap H (prior E) = 0 → ∀ hc : Complete (twirled H (prior E)),
      ∀ rho : Op n d, IsDensityMatrix rho →
        (∫ S, snapshotInverse (twirled H (prior E)) hc S ∂posteriorOf (prior E) rho) = rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
