-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_fermi_dirac_thermodynamics
-- name    : QAlgorithms.Papers.Independent.Next46.P23.fermi_dirac_thermodynamics
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T20:04:52.431985+00:00
-- url     : https://prove2.me/theorems/0141bb2c-897f-4e9f-a693-752464cb5a9c
-- title:
--   §6.3: grand-canonical quasi-free state and thermodynamics
-- statement:
--   For a self-adjoint one-particle Hamiltonian $h$ on finite-dimensional $K$ and real $\beta,\mu$, set $H=d\Gamma(h)$, $N=d\Gamma(I)$ and $\rho_{\beta,\mu}=e^{-\beta(H-\mu N)}/\operatorname{tr}e^{-\beta(H-\mu N)}$. Then this is the quasi-free state with $$T_{\beta,\mu}=(I+e^{\beta(h-\mu I)})^{-1}.$$ Its energy and charge are $E=\operatorname{tr}(hT_{\beta,\mu})$ and $q=\operatorname{tr}(T_{\beta,\mu})$; its pressure is $P=\operatorname{tr}\log(I+e^{-\beta(h-\mu I)})$, and its entropy satisfies $S=\beta(E-\mu q)+P$. These finite thermodynamic identities require no positivity restriction on $\beta$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 126, §6.3: grand-canonical quasi-free state and thermodynamics

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Grand-canonical free Fermi gas and its thermodynamics, source PDF p.126 (6.9).
Both beta and mu are arbitrary real numbers. -/
theorem fermi_dirac_thermodynamics (n : ℕ) (h : Mat (Fin n)) (hh : h.IsHermitian)
    (beta mu : ℝ) :
    let T := fermiDirac h beta mu
    let H := dGamma h
    let N := dGamma (1 : Mat (Fin n))
    let rhoG := QAlgorithms.gibbsState ((-(beta : ℂ)) • (H-(mu : ℂ) • N))
    rhoG = quasiFree T ∧
    ev rhoG H = (h*T).trace.re ∧ ev rhoG N = T.trace.re ∧
    Real.log ((NormedSpace.exp ((-(beta : ℂ)) • (H-(mu : ℂ) • N))).trace.re) =
      (logMat (1+NormedSpace.exp ((-(beta : ℂ)) • (h-(mu : ℂ) • 1)))).trace.re ∧
    entropy rhoG = beta * (ev rhoG H - mu * ev rhoG N) +
      Real.log ((NormedSpace.exp ((-(beta : ℂ)) • (H-(mu : ℂ) • N))).trace.re) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
