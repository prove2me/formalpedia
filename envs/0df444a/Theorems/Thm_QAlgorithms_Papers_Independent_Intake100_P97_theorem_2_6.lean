-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_theorem_2_6
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.theorem_2_6
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:07:38.723046+00:00
-- url     : https://prove2.me/theorems/db7263ea-a9e4-4839-815e-7a071b82aea6
-- title:
--   Theorem 2.6 (1)–(4),(6)–(7): NESS fluctuation theory
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix weights $l_n>0$ with $\sum_n l_n=1$. Write $X_l=\{x:\sum_n l_nx_n^2<\infty\}$ and $X_l^*=\{y:\sum_n l_n^{-1}y_n^2<\infty\}$. Let $D$ be a covariance and let $L:K\to K$ be bounded real linear with $L^*X_l^*\subset X_l^*$. Extend $L$ continuously to $X_l$, and define $\phi^t x=e^{tL}x$ on $X_l$ and $\phi^t x=x$ elsewhere. Put $D_t=e^{tL}De^{tL^*}$, $\omega=\omega_D$ and $\omega_t=\omega_{D_t}$. Assume (G1): $T_t=D_t^{-1}-D^{-1}$ is trace class for every real $t$ and is differentiable at zero in trace norm. Put $\varsigma=(L^*D^{-1}+D^{-1}L)/2=-\dot T_0/2$ and $\sigma=q_{\varsigma}-\operatorname{tr}(D\varsigma)$, where $q_A$ is the canonical Gaussian quadratic observable. Assume also (G2) and (G3): $0<m<M$ and $mI\le D_t\le MI$ for every real $t$, and $D_t$ converges strongly to $D_+$ and $D_-$ as $t\to+\infty$ and $t\to-\infty$, respectively. Write $\omega_\pm=\omega_{D_\pm}$. Assume (G4): a real unitary involution $\theta$ acts continuously on $X_l$ and satisfies $\theta L=-L\theta$ and $\theta D=D\theta$. Put $p=\omega_+(\sigma)$ and $e_t^+(\alpha)=\log\omega_+(e^{-\alpha\ell_t})$, where $\ell_t=\tfrac12\log\det(I+DT_t)-\tfrac12q_{T_t}$ is the canonical logarithmic density. Define $J_t^+=\{\alpha:D_+^{-1}-\alpha T_t>0\}$, and let $J^+$ be the interior of its eventual set-liminf. Each $e_t^+$ is convex; $J_t^+$ is an open interval containing $(-\delta_0,\delta_0)$, with $\delta_0=m/(M-m)$, and $e_t^+$ is real analytic there and $+\infty$ elsewhere.
--
--   The set $J^+$ is also an open interval containing $(-\delta_0,\delta_0)$, and
--
--   $$e_+(\alpha)=\lim_{t\to\infty}t^{-1}e_t^+(\alpha)$$
--
--   exists and is real analytic on $J^+$. Outside its closure, $\limsup_{t\to\infty}t^{-1}e_t^+(\alpha)=+\infty$. The rate $I^+(s)=\sup_{-\alpha\in J^+}\{\alpha s-e_+(-\alpha)\}$ is convex, nonnegative, and zero exactly at $p$. There is an open interval $S$ containing $p$ such that every open $U\subset S$ satisfies
--
--   $$\lim_{t\to\infty}\frac1t\log\omega_+\!\left\{x:\frac1t\int_0^t\sigma_s(x)\,ds\in U\right\}=-\inf_{s\in U}I^+(s).$$
--
--   The time average converges to $p$ for $\omega_+$-almost every $x$. If $J,e,I$ are the reference-state domain, limit and rate, then $e_+=e$ on $J^+\cap J$, and $I^+=I$ on an open interval about $p$ contained in $S$. These are clauses (1)–(4),(6)–(7), including the refined neighborhood around the positive mean.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 9, Theorem 2.6 (1)–(4),(6)–(7): NESS fluctuation theory

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Theorem 2.6(1)–(4),(6)–(7), PDF pp.9–10, with the proof on p.32.
The printed n→∞ in (6) is changed to t→∞, as required by its time variable,
(19), and the proof. The defective printed CLT (5) is separately deferred.
No global Gallavotti–Cohen symmetry is asserted for the NESS rate. -/
theorem theorem_2_6 (e : ℕ ≃ G) (l : G → ℝ) (hl : IsWeight l)
    (D L theta : RealCoordinateOperator G) (hD : IsCovariance D)
    (hL : ∀ y : RealCoordinateHilbert G, inDual l y → inDual l (ContinuousLinearMap.adjoint L y))
    (hG1 : G1 D L) (m M : ℝ) (hG2 : G2 D L m M) (hG3 : G3 D L)
    (hG4 : G4 l D L theta) :
    let mu := cylinderGaussian (futureCovariance D L)
    let mean := ∫ x, production e D L x ∂mu
    let Jp := minimalNessDomain D L
    let ep := limitingNessCumulant e D L
    let Ip := rateFunction Jp ep
    let Iref := rateFunction (minimalDomain D L) (limitingCumulant D L)
    (∀ t, ExtendedConvexOn Set.univ (nessCumulant e D L t)) ∧
    (∀ t, IsOpen (nessDomain D L t) ∧ Convex ℝ (nessDomain D L t) ∧
      Set.Ioo (-m / (M - m)) (m / (M - m)) ⊆ nessDomain D L t ∧
      AnalyticOnNhd ℝ (fun alpha => (nessCumulant e D L t alpha).toReal) (nessDomain D L t) ∧
      (∀ alpha ∈ nessDomain D L t, nessCumulant e D L t alpha =
        (((nessCumulant e D L t alpha).toReal : ℝ) : EReal)) ∧
      (∀ alpha ∉ nessDomain D L t, nessCumulant e D L t alpha = ⊤)) ∧
    IsOpen Jp ∧ Convex ℝ Jp ∧ Set.Ioo (-m / (M - m)) (m / (M - m)) ⊆ Jp ∧
    (∀ alpha ∈ Jp,
      Tendsto (fun t => ((t⁻¹ : ℝ) : EReal) * nessCumulant e D L t alpha)
        atTop (𝓝 (ep alpha : EReal))) ∧
    AnalyticOnNhd ℝ ep Jp ∧
    (∀ alpha ∉ closure Jp,
      Filter.limsup (fun t => ((t⁻¹ : ℝ) : EReal) * nessCumulant e D L t alpha) atTop = ⊤) ∧
    ExtendedConvexOn Set.univ Ip ∧ (∀ s, 0 ≤ Ip s) ∧ (∀ s, Ip s = 0 ↔ s = mean) ∧
    (∃ S : Set ℝ, IsOpen S ∧ Convex ℝ S ∧ mean ∈ S ∧
      (∀ U : Set ℝ, IsOpen U → U ⊆ S →
        Tendsto (fun t => logEventRate mu e l D L t U) atTop
          (𝓝 (-sInf (Ip '' U)))) ∧
      (∃ V : Set ℝ, IsOpen V ∧ Convex ℝ V ∧ mean ∈ V ∧ V ⊆ S ∧
        ∀ s ∈ V, Ip s = Iref s)) ∧
    (∀ᵐ x ∂mu,
      (∀ t : ℝ, IntervalIntegrable (fun s => production e D L (flow l L s x)) volume 0 t) ∧
      Tendsto (fun t => productionAverage e l D L t x) atTop (𝓝 mean)) ∧
    (∀ alpha ∈ Jp ∩ minimalDomain D L, ep alpha = limitingCumulant D L alpha) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
