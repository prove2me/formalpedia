-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_shadowSecondMoment_threeCopies
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.shadowSecondMoment_threeCopies
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:59:51.090744+00:00
-- url     : https://prove2.me/theorems/5bf3791c-fe00-405f-a29f-a53b6b25da1b
-- title:
--   Three-copy formula for the state-dependent second moment
-- statement:
--   Consider the fixed projective experiment on $N$ qudits, $d\ge2$, with locally conjugation-invariant prior $\nu$ and invertible channel $\mathcal M$. Let $\rho$ be a density matrix and $O$ a traceless Hermitian observable. Put $R=\mathcal M^{-1}(O)$, $\hat o(S)=\operatorname{Tr}(O\mathcal M^{-1}(S))$, and $Q_\rho(O)=\mathbb E_{S\mid\rho}\hat o(S)^2$. For $g,h\in(S_3)^N$, let $\chi_g$ permute the three copies independently at each site and $W_h^{(3)}=\mathbb E_\nu\operatorname{Tr}(S^{\otimes3}\chi_h)$. Then
--
--   $$\operatorname{Var}\hat o\le Q_\rho(O),\qquad Q_\rho(O)=\sum_{g,h\in(S_3)^N}d^N\operatorname{Tr}[(R\otimes R\otimes\rho)\chi_g]\,\mathrm{Wg}_{g,h}W_h^{(3)}.$$
--
--   The Weingarten coefficient is the product of the local three-copy coefficients. At $d=2$ the usual spectral extension omits the three-row partition instead of inverting a singular Gram matrix. The equality is expressed over $\mathbb C$ to retain the individual permutation traces. This is a state-dependent second moment, not a worst-state supremum.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 4, §II B, Eqs.(14)–(17): state-dependent shadow second moment

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

/-- PDF pp.4–5 Eqs.(14)–(17): the state-dependent second moment in (S_3)^N.
For qubits wgThree uses its spectral extension at the singular Gram matrix. -/
theorem shadowSecondMoment_threeCopies {n d : ℕ} (hd : 2 ≤ d) (E : ProjectiveEnsemble n d)
    (hls : LocallyScrambled (prior E)) (hc : Complete (prior E))
    (rho O : Op n d) (hrho : IsDensityMatrix rho) (hO : O.IsHermitian) (ht : O.trace = 0) :
    shotVariance (prior E) hc rho O ≤ secondMoment (prior E) hc rho O ∧
    (secondMoment (prior E) hc rho O : ℂ) =
      ∑ g : Permutations n 3, ∑ h : Permutations n 3,
        observableThree (prior E) hc rho O g * (productWgThree d g h : ℂ) *
          featureThree (prior E) h := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
