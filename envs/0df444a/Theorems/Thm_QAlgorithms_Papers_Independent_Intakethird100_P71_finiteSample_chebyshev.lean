-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P71_finiteSample_chebyshev
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P71.finiteSample_chebyshev
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:01:06.377203+00:00
-- url     : https://prove2.me/theorems/fa1a668b-422d-420e-a0ef-5182aaa0390b
-- title:
--   Finite-sample Chebyshev guarantee
-- statement:
--   Fix a locally scrambled, tomographically complete projective experiment on $N$ qudits, $d\ge2$, a density matrix $\rho$, and a traceless Hermitian observable $O$. Let $\hat o$ be its unbiased single-shot shadow prediction, $Q_\rho(O)=\mathbb E\hat o^2$, and $\bar o$ the arithmetic mean of $M\ge1$ independent snapshots of identical copies. For $\epsilon>0$ and $0<\delta<1$,
--
--   $$\Pr\bigl(|\bar o-\operatorname{Tr}(O\rho)|\ge\epsilon\bigr)\le\frac{\operatorname{Var}\hat o}{\epsilon^2 M}\le\frac{Q_\rho(O)}{\epsilon^2 M}.$$
--
--   In particular,
--
--   $$M\ge\frac{Q_\rho(O)}{\epsilon^2\delta}\quad\Longrightarrow\quad\Pr\bigl(|\bar o-\operatorname{Tr}(O\rho)|\ge\epsilon\bigr)\le\delta.$$
--
--   This is a sufficient copy count for the specified state and observable.
-- source:
--   Classical Shadow Tomography with Locally Scrambled Quantum Dynamics, arXiv:2107.04817v4, PDF p. 5, §II B, Eqs.(18)–(19): finite-sample Chebyshev guarantee

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

/-- PDF p.5 Eqs.(18)–(19): Chebyshev and its sufficient copy count for each
specified rho and O. No necessary bound or simultaneous-observable claim. -/
theorem finiteSample_chebyshev {n d : ℕ} (hd : 2 ≤ d) (E : ProjectiveEnsemble n d)
    (hls : LocallyScrambled (prior E)) (hc : Complete (prior E))
    (rho O : Op n d) (hrho : IsDensityMatrix rho) (hO : O.IsHermitian) (ht : O.trace = 0)
    (m : ℕ) (hm : 0 < m) (eps delta : ℝ) (heps : 0 < eps)
    (hdelta : 0 < delta ∧ delta < 1) :
    let failure := (snapshotSampleLaw (prior E) rho m)
      {s | eps ≤ |shadowSampleMean (prior E) hc O s - (O*rho).trace.re|}
    failure ≤ ENNReal.ofReal (shotVariance (prior E) hc rho O / (eps^2 * m)) ∧
    shotVariance (prior E) hc rho O / (eps^2 * m) ≤
      secondMoment (prior E) hc rho O / (eps^2 * m) ∧
    (secondMoment (prior E) hc rho O / (eps^2 * delta) ≤ m →
      failure ≤ ENNReal.ofReal delta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P71

end
