-- Prove2me | Theorems.Thm_SelfStructIS_LogEff_theorem_5_1
-- name    : SelfStructIS.LogEff.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:30:18.05899+00:00
-- url     : https://prove2.me/theorems/4e7a58ba-cf82-4a28-b25b-52941f911b99
-- title:
--   Theorem 5.1, p. 16 — the self-structuring IS estimator is logarithmically efficient
-- statement:
--   Let $X$ be a random vector in $\mathbb R^d$ with density $f_X$, satisfying Assumptions 3.1, 3.2 and 5.1, and suppose the limit $q^*=\lim_{t\to\infty}\hat q(t)$ exists. Let the measurable loss $L$ satisfy Assumption 2.1 with index $\rho$ and limit $L^*$, and suppose $L^*(q^*x)$ is not identically zero on $\mathbb R^d_+$: $L^*(q^*x)>0$ for some $x\in\mathbb R^d_+$. Let the hyper-parameter $l=l(u)$ be slowly varying in $u$ with $l(u)\to\infty$, and fix either exponent $\kappa=\kappa^{(1)}$ or $\kappa=\kappa^{(2)}$. Then the estimators $\{\zeta(u):u>0\}$ are logarithmically efficient for $p_u=P(L(X)\ge u)$: $M_{2,u}=E[\zeta(u)^2]$ is finite for all large $u$, and
--   $$\lim_{u\to\infty}\frac{\log M_{2,u}}{\log p_u^2}=1.\qquad(23)$$
--
--   Since $M_{2,u}\ge p_u^2$ always, (23) says the relative error of the self-structuring sampler grows more slowly than any power $p_u^{-\varepsilon}$, while plain Monte Carlo's grows like $p_u^{-1/2}$. The sampler needs no knowledge of the density and only black-box evaluations of $L$.
--
--   **Formalization Note** "Assumptions 3.1 – 5.1" are Assumptions 3.1, 3.2 and 5.1. The requirement $l(u)\to\infty$ is not in the printed statement but in §2.2, p. 9 (which states the same result for "$l=l(u)$ … slowly varying in $u$ and satisfying $\lim_{u\to\infty}l(u)=+\infty$"), and the proof uses it (Lemma A.5, App. D.1). "Not identically zero" is read as positivity somewhere, which is what gives $I^*<\infty$. The conjunct $M_{2,u}<\infty$ makes explicit what $\log M_{2,u}$ presupposes, so that a junk value $\log(+\infty)$ cannot satisfy (23). $M_{2,u}$ and $p_u$ are extended reals; the ratio is of real logarithms of their real values.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 16, Theorem 5.1, (23) (proof App. A.3, pp. 33–35, and App. E, pp. 48–49)

import Mathlib
import Definitions.Def_HeavyTailNV_Tail_Model
import Definitions.Def_SelfStructIS_LogEff_Setting
import Definitions.Def_SelfStructIS_LogEff_Sampler

open MeasureTheory Filter Topology

namespace SelfStructIS.LogEff

theorem theorem_5_1 (d : ℕ) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (fX : (Fin d → ℝ) → ℝ) (hfX_meas : Measurable fX) (hfX_nonneg : ∀ x, 0 ≤ fX x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (fX x)))
    (α : Fin d → ℝ) (h31 : Assumption31 μ α)
    (p φ I : (Fin d → ℝ) → ℝ) (h32 : Assumption32 μ p φ I)
    (h51 : Assumption51 μ)
    (qstar : Fin d → ℝ) (hqstar : Tendsto (qhat μ) atTop (𝓝 qstar))
    (L Lstar : (Fin d → ℝ) → ℝ) (ρ : ℝ) (hL : Measurable L) (h21 : Assumption21 μ L ρ Lstar)
    (hLstar : ∃ x : Fin d → ℝ, (∀ i, 0 ≤ x i) ∧ 0 < Lstar (qstar * x))
    (l : ℝ → ℝ) (hl_sv : SlowlyVarying l) (hl_top : Tendsto l atTop atTop)
    (c : KappaChoice) :
    (∀ᶠ u in atTop, M2 μ fX L ρ c u (l u) < ⊤) ∧
      Tendsto (fun u => Real.log (M2 μ fX L ρ c u (l u)).toReal /
        Real.log ((pu μ L u).toReal ^ 2)) atTop (𝓝 1) := by sorry

end SelfStructIS.LogEff
