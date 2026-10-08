-- Prove2me | Theorems.Thm_ProbMetricStab_TwoStage_corollary_2_8
-- name    : ProbMetricStab.TwoStage.corollary_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:48.740993+00:00
-- url     : https://prove2.me/theorems/4f26ca25-9d1c-4d20-9e47-41752d9ad252
-- title:
--   Corollary 2.8, p. 10 — Lipschitz stability of v and S in ζ_g for convex programs with ℱ_g-integrands
-- statement:
--   Consider the stochastic program $\min\{\int_\Xi f_0(\xi,x)\,\mu(d\xi):x\in X\}$ under the general assumptions: $X\subseteq\mathbb R^m$ is nonempty and closed, $\Xi\subseteq\mathbb R^s$ is closed, and $f_0:\Xi\times\mathbb R^m\to\overline{\mathbb R}$ is a normal integrand. Let $\xi_0\in\Xi$, let $g:\mathbb R_+\to\mathbb R_+$ be nondecreasing with $g(0)=0$, and let $\mu\in\mathcal P_g(\Xi)$. Assume
--
--   1. $S(\mu)$ is nonempty and $\mathcal U$ is an open, bounded neighbourhood of $S(\mu)$;
--   2. $X$ is convex and $f_0(\xi,\cdot)$ is convex on $\mathbb R^m$ for each $\xi\in\Xi$;
--   3. there is a constant $L>0$ such that $\frac1Lf_0(\cdot,x)\in\mathcal F_g(\Xi)$ for each $x\in X\cap\operatorname{cl}\mathcal U$;
--   4. (disclosed) $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$.
--
--   Then there is $\delta>0$ such that, whenever $\nu\in\mathcal P_g(\Xi)\cap\mathcal P_{\mathcal F_{\mathcal U}}(\Xi)$ and $\zeta_g(\mu,\nu)<\delta$, the optimal values $v(\mu)$, $v(\nu)$ are finite and
--
--   $$|v(\mu)-v(\nu)|\le L\,\zeta_g(\mu,\nu),\qquad\emptyset\ne S(\nu)\subseteq S(\mu)+\Psi\big(L\,\zeta_g(\mu,\nu)\big)\mathbb B,$$
--
--   where $\Psi(\eta)=\eta+\psi^{-1}(2\eta)$ and $\psi(\tau)=\min\{\int_\Xi f_0(\xi,x)\,\mu(d\xi)-v(\mu):d(x,S(\mu))\ge\tau,\ x\in X\cap\operatorname{cl}\mathcal U\}$.
--
--   This is the bridge from the general stability theorems of Section 2 to a concrete, model-adapted (canonical) probability metric; Theorem 3.3 is its instance with $g(t)=t$.
--
--   **Formalization Note** The constant $L$ in the conclusion is the $L$ of assumption 3; only $\delta$ is existential. Assumption 3 is read as: $f_0(\xi,x)$ is finite for $\xi\in\Xi$ and the real function $\xi\mapsto f_0(\xi,x)/L$ satisfies the $\mathcal F_g$ inequality. The proof on p. 10 invokes Theorem 2.2, whose assumptions include $\mu\in\mathcal P_{\mathcal F_{\mathcal U}}$, and the conclusion of Theorem 2.2 concerns $\nu\in\mathcal P_{\mathcal F_{\mathcal U}}$; the printed hypotheses do not obviously imply either (the lower integrability of $\inf_{\|x\|\le r}f_0$ involves points outside $\operatorname{cl}\mathcal U$), so both memberships are added as hypotheses. The inclusion $S(\nu)\subseteq S(\mu)+\Psi\mathbb B$ is written as: every $x\in S(\nu)$ has some $y\in S(\mu)$ at distance at most $\Psi(L\zeta_g(\mu,\nu))\in[0,\infty]$. The finiteness of $v(\mu),v(\nu)$ is stated explicitly because the paper's real inequality asserts it.
-- source:
--   Rachev & Römisch, Quantitative stability in stochastic programming: The method of probability metrics, preprint (edoc.hu-berlin.de), p. 10, Corollary 2.8 (general assumptions: p. 2)

import Mathlib
import Definitions.Def_ProbMetricStab_TwoStage_Setting

open scoped ENNReal NNReal

namespace ProbMetricStab.TwoStage

/-- Corollary 2.8 (p. 10), for model (1) with `d = 0`. General assumptions: `X ⊆ ℝ^m` nonempty and
closed, `Ξ ⊆ ℝ^s` closed, `f₀` a normal integrand. Let `ξ₀ ∈ Ξ`, `g : ℝ₊ → ℝ₊` nondecreasing with
`g(0) = 0`, `μ ∈ 𝒫_g(Ξ)`, and assume (i) `S(μ) ≠ ∅` and `𝒰` is an open bounded neighbourhood of
`S(μ)`; (ii) `X` is convex and `f₀(ξ, ·)` is convex for each `ξ ∈ Ξ`; (iii) `L > 0` and
`(1/L) f₀(·, x) ∈ ℱ_g` (in particular `f₀(·, x)` is finite on `Ξ`) for each `x ∈ X ∩ cl 𝒰`.
Disclosed pin: `μ` and the perturbations `ν` lie in `𝒫_{ℱ_𝒰}(Ξ)` (an assumption of Theorem 2.2,
which the proof invokes). Then there is `δ > 0` such that, whenever `ν ∈ 𝒫_g(Ξ)` and
`ζ_g(μ, ν) < δ`, `v(μ), v(ν)` are finite with `|v(μ) − v(ν)| ≤ L ζ_g(μ, ν)` and
`∅ ≠ S(ν) ⊆ S(μ) + Ψ(L ζ_g(μ, ν)) 𝔹`. -/
theorem corollary_2_8 {m s : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (Ξ : Set (EuclideanSpace ℝ (Fin s)))
    (f : EuclideanSpace ℝ (Fin s) → EuclideanSpace ℝ (Fin m) → EReal)
    (hX : X.Nonempty) (hXc : IsClosed X) (hΞ : IsClosed Ξ) (hf : IsNormalIntegrand Ξ f)
    (ξ₀ : EuclideanSpace ℝ (Fin s)) (hξ₀ : ξ₀ ∈ Ξ) (g : ℝ≥0 → ℝ≥0) (hg : Monotone g)
    (hg0 : g 0 = 0) (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin s))) (hμ : μ ∈ Pg Ξ g)
    (U : Set (EuclideanSpace ℝ (Fin m)))
    (hS : (S X Ξ f μ).Nonempty) (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hSU : S X Ξ f μ ⊆ U)
    (hXconv : Convex ℝ X) (hfconv : ∀ ξ ∈ Ξ, Convex ℝ (epi (f ξ)))
    (L : ℝ) (hL : 0 < L)
    (hfin : ∀ x ∈ X ∩ closure U, ∀ ξ ∈ Ξ, f ξ x ≠ ⊤ ∧ f ξ x ≠ ⊥)
    (hFg : ∀ x ∈ X ∩ closure U, (fun ξ => (f ξ x).toReal / L) ∈ Fg Ξ ξ₀ g)
    (hμU : μ ∈ PFU X Ξ f U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin s)),
      ν ∈ Pg Ξ g → ν ∈ PFU X Ξ f U → zetaG Ξ ξ₀ g μ ν < ENNReal.ofReal δ →
        (v X Ξ f μ ≠ ⊤ ∧ v X Ξ f μ ≠ ⊥ ∧ v X Ξ f ν ≠ ⊤ ∧ v X Ξ f ν ≠ ⊥ ∧
          |(v X Ξ f μ).toReal - (v X Ξ f ν).toReal| ≤ L * (zetaG Ξ ξ₀ g μ ν).toReal) ∧
        (S X Ξ f ν).Nonempty ∧
        ∀ x ∈ S X Ξ f ν, ∃ y ∈ S X Ξ f μ,
          edist x y ≤ Psi X Ξ f μ U (ENNReal.ofReal L * zetaG Ξ ξ₀ g μ ν) := by sorry

end ProbMetricStab.TwoStage
