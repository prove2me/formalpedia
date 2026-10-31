-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_theorem_2_4
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.theorem_2_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:07:04.247841+00:00
-- url     : https://prove2.me/theorems/9ba21dcf-6d3a-4207-a1d4-98654b32bd2f
-- title:
--   Theorem 2.4 (1)–(3),(5): reference-state fluctuations and strong law
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Assume also (G2) and (G3): $0<m<M$ and $mI\le D_t\le MI$ for every real $t$, and $D_t$ converges strongly to $D_+$ and $D_-$ as $t\to+\infty$ and $t\to-\infty$, respectively. Write $\omega_\pm=\omega_{D_\pm}$. Assume (G4): a real unitary involution $\theta$ acts continuously on $X_l$ and satisfies $\theta L=-L\theta$ and $\theta D=D\theta$. Let $\sigma_s=\sigma\circ\phi^s$, $p=\omega_+(\sigma)$, and $e_t(\alpha)=\log\omega(e^{\alpha\ell_t})$, with extended logarithms. Let $J$ be the open minimal interval, the interior of the eventual finite-time positivity domains, and define $e(\alpha)=\lim_{t\to\infty}t^{-1}e_t(\alpha)$ for $\alpha\in J$. Then the limit exists, $[0,1]\subset J$, $e$ is convex, and
--
--   $$e(0)=e(1)=0,\quad e^{\prime}(0)=-p\le0,\quad e^{\prime}(1)=p\ge0,\quad e(1-\alpha)=e(\alpha).$$
--
--   The function extends analytically to the two open half-planes together with $J$. There is a unique signed locally finite Borel measure $\nu$ supported in $\mathbb R\setminus J$, with $\int |r|^{-1}\,d|\nu|(r)<\infty$, such that
--
--   $$e(\alpha)=-\int_{\mathbb R}\log(1-\alpha/r)\,d\nu(r).$$
--
--   The rate $I(s)=\sup_{-\alpha\in J}\{\alpha s-e(-\alpha)\}$ is convex, takes values in $[0,\infty]$, is zero exactly at $p$, and obeys $I(-s)=I(s)+s$. There is $\varepsilon>0$ such that every open $U\subset(-p-\varepsilon,p+\varepsilon)$ satisfies
--
--   $$\lim_{t\to\infty}\frac1t\log\omega\!\left\{x:\frac1t\int_0^t\sigma_s(x)\,ds\in U\right\}=-\inf_{s\in U}I(s).$$
--
--   For $\omega$-almost every $x$, $t^{-1}\int_0^t\sigma_s(x)\,ds\to p$. These are precisely clauses (1)–(3),(5); the printed CLT is inventoried separately.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 7, Theorem 2.4 (1)–(3),(5): reference-state fluctuations and strong law

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Theorem 2.4(1)–(3),(5), PDF pp.7–8, proof pp.21–24.
The minimal interval uses the interior of the raw set-liminf as the proof does;
no assertion excludes endpoints from that raw set-liminf. The signed logarithmic
potential permits infinite unweighted variation. Printed CLT (4) is separately deferred. -/
theorem theorem_2_4 (e : ℕ ≃ G) (l : G → ℝ) (hl : IsWeight l)
    (D L theta : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) (m M : ℝ) (hG2 : G2 D L m M) (hG3 : G3 D L)
    (hG4 : G4 l D L theta) :
    let J := minimalDomain D L
    let f := limitingCumulant D L
    let I := rateFunction J f
    let mean := ∫ x, production e D L x ∂cylinderGaussian (futureCovariance D L)
    Set.Icc (0 : ℝ) 1 ⊆ J ∧
    (∀ alpha ∈ J,
      Tendsto (fun t => ((t⁻¹ : ℝ) : EReal) * gaussianCumulant D L t alpha)
        atTop (𝓝 (f alpha : EReal))) ∧
    ConvexOn ℝ J f ∧ f 0 = 0 ∧ f 1 = 0 ∧
    deriv f 0 = -mean ∧ deriv f 1 = mean ∧ 0 ≤ mean ∧
    (∀ alpha ∈ J, f (1 - alpha) = f alpha) ∧
    (∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (gaussianCutPlane J) ∧
      ∀ alpha ∈ J, F (alpha : ℂ) = (f alpha : ℂ)) ∧
    (∃! nu : SignedBorelPair, LogPotential J f nu) ∧
    ExtendedConvexOn Set.univ I ∧ (∀ s, 0 ≤ I s) ∧ (∀ s, I s = 0 ↔ s = mean) ∧
    (∀ s, I (-s) = I s + (s : EReal)) ∧
    (∃ epsilon : ℝ, 0 < epsilon ∧ ∀ U : Set ℝ,
      IsOpen U → U ⊆ Set.Ioo (-mean - epsilon) (mean + epsilon) →
        Tendsto (fun t => logEventRate (cylinderGaussian D) e l D L t U) atTop
          (𝓝 (-sInf (I '' U)))) ∧
    (∀ᵐ x ∂cylinderGaussian D,
      (∀ t : ℝ, IntervalIntegrable (fun s => production e D L (flow l L s x)) volume 0 t) ∧
      Tendsto (fun t => productionAverage e l D L t x) atTop (𝓝 mean)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
