-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_proposition_2_1
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.proposition_2_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:04:25.615991+00:00
-- url     : https://prove2.me/theorems/a3677dff-1221-4aeb-9786-a0f26eb55874
-- title:
--   Proposition 2.1 (all five clauses)
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Write $\sigma_t=\sigma\circ\phi^t$, $\ell_t=\log(d\omega_t/d\omega)$ and $\rho_t=e^{\ell_t}$. Then all of the following hold.
--
--   1. Each $\sigma_t$ is integrable and $t\mapsto\sigma_t$ is continuous in $L^1(\omega)$.
--
--   2. $\ell_t=\int_0^t\sigma_{-s}\,ds$ in $L^1(\omega)$, as the integral of a continuous Banach-valued function, and also pointwise for $\omega$-almost every $x$, with the real integral integrable on the time interval.
--
--   3. The actual density is a $C^1$ map into $L^1(\omega)$, with
--
--   $$\frac{d}{dt}\rho_t=\rho_t\sigma_{-t}.$$
--
--   4. The observable is integrable for each $\omega_t$ and $\omega_t(\sigma)=\operatorname{tr}(\varsigma(D_t-D))$, in particular $\omega(\sigma)=0$.
--
--   5. $\operatorname{Ent}(\omega_t\mid\omega)=-\int_0^t\omega_s(\sigma)\,ds$.
--
--   This gives the density differentiability and trace-expectation interface without adding (G2)–(G4).
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 5, Proposition 2.1 (all five clauses)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Proposition 2.1, all five clauses including the C¹ L¹ density derivative (9),
PDF pp.5–6. Continuous Banach-valued interval integrals also represent the source's Riemann integral. -/
theorem proposition_2_1 (e : ℕ ≃ G) (l : G → ℝ) (hl : IsWeight l)
    (D L : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) :
    let mu := cylinderGaussian D
    let sig := fun t x => production e D L (flow l L t x)
    let rho := fun t => realRNDensity (cylinderGaussian (covarianceAt D L t)) mu
    let ell := fun t x => Real.log (rho t x)
    (∀ t, Integrable (sig t) mu) ∧
    Continuous (fun t => asL1 mu (sig t)) ∧
    (∀ t, Integrable (ell t) mu ∧
      asL1 mu (ell t) = ∫ s in (0 : ℝ)..t, asL1 mu (sig (-s))) ∧
    (∀ t, ∀ᵐ x ∂mu, IntervalIntegrable (fun s => sig (-s) x) volume 0 t ∧
      ell t x = ∫ s in (0 : ℝ)..t, sig (-s) x) ∧
    (∀ t, Integrable (rho t) mu ∧ Integrable (fun x => rho t x * sig (-t) x) mu) ∧
    ContDiff ℝ 1 (fun t => asL1 mu (rho t)) ∧
    (∀ t, HasDerivAt (fun s => asL1 mu (rho s))
      (asL1 mu (fun x => rho t x * sig (-t) x)) t) ∧
    (∀ t, Integrable (production e D L) (cylinderGaussian (covarianceAt D L t)) ∧
      (∫ x, production e D L x ∂cylinderGaussian (covarianceAt D L t)) =
        basisOperatorTrace (productionOperator D L * (covarianceAt D L t - D))) ∧
    (∫ x, production e D L x ∂mu) = 0 ∧
    (∀ t, nonpositiveRelativeEntropy (cylinderGaussian (covarianceAt D L t)) mu =
      (((- ∫ s in (0 : ℝ)..t,
        ∫ x, production e D L x ∂cylinderGaussian (covarianceAt D L s)) : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
