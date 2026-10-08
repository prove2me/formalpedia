-- Prove2me | Theorems.Thm_SAARate_SharpLD_display_3_15
-- name    : SAARate.SharpLD.display_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:44.735977+00:00
-- url     : https://prove2.me/theorems/4bf4112e-d946-4f8b-9874-cd3115b70988
-- title:
--   (3.15), p. 12 — β := inf_{z∈F} I(z) ≥ c²/(2κ²)
-- statement:
--   Let $P$ be a probability measure on a measurable space $(\Omega,\mathcal F)$, let $h:\mathbb R^m\times\Omega\to\mathbb R$, and let $\Theta\subseteq\mathbb R^m$. Write $f(x)=\mathbb E_P\,h(x,\omega)$ for the true objective (1.1) and $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$ for the sample average objective (1.2) built from an i.i.d. sample $\omega^1,\omega^2,\dots$ with law $P$. The assumptions of Theorem 2.1 are: (i) $h(\cdot,\omega)$ is convex for every $\omega$; (ii) $f$ is well defined and finite valued; (iii) $\Theta$ is closed and convex; (iv) Assumption (A): $f$ has the unique minimizer $\bar x$ on $\Theta$ and there is $c>0$ with $f(x)\ge f(\bar x)+c\|x-\bar x\|$ for all $x\in\Theta$. Assumption (B) asks for a $\kappa>0$ with $\sup_{d\in S^{m-1}}|h'_\omega(\bar x,d)|\le\kappa$ for $P$-almost every $\omega$, where $h'_\omega(\bar x,d)$ is the directional derivative of $h(\cdot,\omega)$ at $\bar x$ in direction $d$ and $S^{m-1}$ is the unit sphere.
--
--   Suppose (i)–(iv) hold, that $c>0$ satisfies (2.2), and that Assumption (B) holds with constant $\kappa$. Let $Z=C(S^{m-1})$, let $I$ be the rate function (3.4) of the $Z$-valued random element $\eta(\cdot,\omega)=h'_\omega(\bar x,\cdot)$, and let
--   $$F=\Bigl\{z\in Z:\inf_{d\in T_\Theta(\bar x)\cap S^{m-1}}z(d)\le0\Bigr\}$$
--   be the set (3.9). Then the constant $\beta$ of (3.10) satisfies
--   $$\beta:=\inf_{z\in F}I(z)\ \ge\ \frac{c^2}{2\kappa^2}.$$
--
--   Together with the upper bound of Cramér's theorem in $Z$ and the reduction $P(\mathcal E_N^c)\le P(\zeta_N\in F)$ this gives Theorem 3.1 with the explicit exponent $c^2/(2\kappa^2)$.
--
--   **Formalization Note** The infimum is taken in the extended reals, so $\beta=+\infty$ when $F$ is empty. $F$ is written with an attained infimum ("some $d\in T_\Theta(\bar x)\cap S^{m-1}$ has $z(d)\le0$"), equivalent for continuous $z$ on the compact set $T_\Theta(\bar x)\cap S^{m-1}$. "f finite valued" is $P$-integrability of every $h(x,\cdot)$. The constant $c$ is a binder with (2.2); the sample plays no role and is omitted.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), p. 12, proof of Theorem 3.1, (3.9), (3.10), (3.15)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_LargeDeviation
import Definitions.Def_SAARate_SharpLD_Setting

open MeasureTheory ProbabilityTheory Filter Topology BellWilliams2001.ThresholdPolicy

namespace SAARate.SharpLD

theorem display_3_15 {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : SAARate.Sharp.E m → Ω → ℝ)
    (hconv : ∀ ω, ConvexOn ℝ Set.univ (fun x => h x ω))
    (hint : ∀ x, Integrable (h x) P)
    (Θ : Set (SAARate.Sharp.E m)) (hΘc : IsClosed Θ) (hΘv : Convex ℝ Θ)
    (xbar : SAARate.Sharp.E m) (hA : SAARate.Sharp.AssumptionA P h Θ xbar)
    (c : ℝ) (hc : 0 < c)
    (h22 : ∀ x ∈ Θ, SAARate.Sharp.expectedObj P h x ≥ SAARate.Sharp.expectedObj P h xbar + c * ‖x - xbar‖)
    (κ : ℝ) (hB : AssumptionB P h xbar κ) :
    ((c ^ 2 / (2 * κ ^ 2) : ℝ) : EReal) ≤
      ⨅ z ∈ failureSetF Θ xbar, cramerRate P (etaZ h xbar) z := by sorry

end SAARate.SharpLD
