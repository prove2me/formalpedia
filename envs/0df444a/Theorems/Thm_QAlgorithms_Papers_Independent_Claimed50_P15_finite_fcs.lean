-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_finite_fcs
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.finite_fcs
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:48:10.582321+00:00
-- url     : https://prove2.me/theorems/eba8f381-9e90-4759-9786-83091f1cfa47
-- title:
--   Finite-system entropy balance and full counting statistics
-- statement:
--   Let $H$ be self-adjoint on a nonzero finite-dimensional complex Hilbert space, let $\omega>0$ have trace one, and put $U_t=e^{-itH}$, $\omega_t=U_t\omega U_t^*$, $S=-\log\omega$, $S_t=U_t^*SU_t$, $\Sigma^t=(S_t-S)/t$, and $e_t(s)=\log\operatorname{Tr}(\omega_t^s\omega^{1-s})$. Let $P_t$ be the two-measurement law of $(\alpha'-\alpha)/t$ for $S$, and let $\mu_{\nu|\omega}$ be the spectral law of $-\log\Delta_{\nu|\omega}$ in $\Omega_\omega$. For $t>0$,
--
--   $$\omega(\Sigma^t)=-\frac{\operatorname{Ent}(\omega_t|\omega)}t\ge0,\quad P_t=(x\mapsto x/t)_*\mu_{\omega_{-t}|\omega},\quad e_t(1-s)=\log\int e^{-st\phi}\,dP_t(\phi).$$
--
--   Here $P_t$ is a probability measure and $\operatorname{Ent}(\nu|\omega)=\operatorname{Tr}\nu(\log\omega-\log\nu)$. For every real $u,s$, $e_{-u}(s)=e_u(1-s)$. The first two moments satisfy
--
--   $$\mathbb E_{P_t}\phi=\omega(\Sigma^t)=e_t'(1)/t,\qquad\operatorname{Var}_{P_t}\phi=\omega((\Sigma^t)^2)-\omega(\Sigma^t)^2=e_t''(1)/t^2.$$
--
--   If one orthonormal basis makes both $H$ and $\omega$ real, then also $e_t(s)=e_t(1-s)=\log\int e^{-st\phi}\,dP_t$, $P_t=(x\mapsto x/t)_*\mu_{\omega_t|\omega}$, and reflection of $P_t$ equals $e^{-t\phi}dP_t$, while reflection of $\mu_{\omega_t|\omega}$ equals $e^{-x}d\mu_{\omega_t|\omega}$. These are pushforward/weighting identities, with no claim about higher cumulants.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 19, Finite-system entropy balance and full counting statistics

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Finite-system entropy balance, physical FCS, its first two moments and
all four TRI fluctuation identities, arXiv:1109.3804v2, PDF pp.19--21,
(4.1)--(4.8). No equality of higher cumulants is asserted. -/
theorem finite_fcs {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (H omega : Matrix I I ℂ) (hH : H.IsHermitian) (homega : omega.PosDef)
    (hnorm : omega.trace = 1) :
    (∀ u s : ℝ, finiteEntropic H omega (-u) s = finiteEntropic H omega u (1 - s)) ∧
    (∀ t : ℝ, 0 < t →
      IsProbabilityMeasure (finiteFCS H omega t) ∧
      evaluate omega (meanProduction H omega t) = -finiteRelativeEntropyNats (evolvedState H omega t) omega / t ∧
      0 ≤ evaluate omega (meanProduction H omega t) ∧
      finiteFCS H omega t = Measure.map (fun x : ℝ => x / t)
        (finiteModularLaw (evolvedState H omega (-t)) omega) ∧
      (∀ s : ℝ, finiteEntropic H omega t (1 - s) =
        Real.log (∫ phi : ℝ, Real.exp (-s * t * phi) ∂finiteFCS H omega t)) ∧
      (∫ phi : ℝ, phi ∂finiteFCS H omega t) = evaluate omega (meanProduction H omega t) ∧
      (∫ phi : ℝ, phi ∂finiteFCS H omega t) = deriv (finiteEntropic H omega t) 1 / t ∧
      ((∫ phi : ℝ, phi ^ 2 ∂finiteFCS H omega t) -
        (∫ phi : ℝ, phi ∂finiteFCS H omega t) ^ 2) =
          evaluate omega (meanProduction H omega t * meanProduction H omega t) -
            (evaluate omega (meanProduction H omega t)) ^ 2 ∧
      ((∫ phi : ℝ, phi ^ 2 ∂finiteFCS H omega t) -
        (∫ phi : ℝ, phi ∂finiteFCS H omega t) ^ 2) =
          deriv (deriv (finiteEntropic H omega t)) 1 / t ^ 2 ∧
      (IsFiniteTRI H omega →
        (∀ s : ℝ, finiteEntropic H omega t s = finiteEntropic H omega t (1 - s)) ∧
        (∀ s : ℝ, finiteEntropic H omega t s =
          Real.log (∫ phi : ℝ, Real.exp (-s * t * phi) ∂finiteFCS H omega t)) ∧
        finiteFCS H omega t = Measure.map (fun x : ℝ => x / t)
          (finiteModularLaw (evolvedState H omega t) omega) ∧
        Measure.map (fun phi : ℝ => -phi) (finiteFCS H omega t) =
          (finiteFCS H omega t).withDensity (fun phi => ENNReal.ofReal (Real.exp (-t * phi))) ∧
        Measure.map (fun x : ℝ => -x) (finiteModularLaw (evolvedState H omega t) omega) =
          (finiteModularLaw (evolvedState H omega t) omega).withDensity
            (fun x => ENNReal.ofReal (Real.exp (-x))))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
