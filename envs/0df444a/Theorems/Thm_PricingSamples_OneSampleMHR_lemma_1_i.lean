-- Prove2me | Theorems.Thm_PricingSamples_OneSampleMHR_lemma_1_i
-- name    : PricingSamples.OneSampleMHR.lemma_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:09.430648+00:00
-- url     : https://prove2.me/theorems/d272c58f-8b66-484f-ae33-bb9c373cd0b5
-- title:
--   Lemma 1 i.), p. 18 (part i; part ii is lemma_1_ii) — local revenue integral ≥ its quantile-space bound through H̃_l^{−1} when v F̄(v) is non-decreasing
-- statement:
--   **Local revenue integrals in quantile space, part i.)** (Lemma 1 has two parts; this item is part i.), and part ii.) is `lemma_1_ii`.)
--
--   Fix $\alpha \in [0,1]$, $F \in \mathcal F_\alpha$ with ccdf $\bar F$ and quantiles $q_w = \bar F(w)$, a non-negative function $g : [0,1] \to \mathbb R_+$, $\gamma > 0$ and $0 \le w < w'$. Let $H_l : \mathbb R_+ \to [0,1]$ be non-increasing with $\bar F \ge H_l$ on $[\gamma w, \gamma w']$. Suppose that
--
--   1. the revenue $v \bar F(v)$ is non-decreasing on $[\gamma w, \gamma w']$, and
--   2. $\tilde H_l : \mathbb R_+ \to [0,1]$ is non-increasing with $\bar F \ge \tilde H_l$ on $[w,w']$, $\tilde H_l(w) = \bar F(w)$ and $\tilde H_l(w') = \bar F(w')$.
--
--   Then
--
--   $$\int_w^{w'} \gamma s\,\bar F(\gamma s)\, g(\bar F(s))\,dF(s) \;\ge\; \int_{q_{w'}}^{q_w} \gamma\,\tilde H_l^{-1}(q)\, H_l\big(\gamma \tilde H_l^{-1}(q)\big)\, g(q)\,dq,$$
--
--   where $\tilde H_l^{-1}(q) = \inf\{x \ge 0 : \tilde H_l(x) \le q\}$ is the generalized inverse.
--
--   The left side is a local contribution to the revenue of posting $\gamma s$ (eq. (5) with $g$ the order-statistic weight); the right side depends on $F$ only through the envelopes. Applied with the generalized Pareto envelopes of Lemma 2 it yields Proposition 2 i.), the bound to the left of the optimal price.
--
--   **Formalization Note** Both integrals are lower Lebesgue integrals of non-negative functions (values in $[0,\infty]$); $dF$ is $\mu$ restricted to $[w,w']$. $g$ is taken measurable.
--
--   Differences from the source:
--
--   - reading: Definition 2 (pp. 11–12): F admits a density f and the virtual value φ_F(v) = v − (1 − F(v))/f(v) satisfies φ_F(v′) − φ_F(v) ≥ α(v′ − v) for all v′ ≥ v in the support S_F → μ ≪ Lebesgue measure, and v ↦ Γ_α^{−1}(F̄(v)) is convex on {v ≥ 0 : F̄(v) > 0}; reason: the paper's own equivalent form, used in the proof of Lemma 2 (p. App-10, after Schweizer–Szech); it avoids evaluating an a.e.-defined density pointwise and takes the support to be an interval, as the paper's proofs do (with a gap in the support, e.g. F̄ = e^{−v} on [0,1], e^{−1} on [1,2], e^{−(v−1)} beyond, the pointwise condition holds at α = 1 but Lemma 2 fails at w = 0, w′ = 2, v = 1.5)
--   - reading: inverses H̃_l^{−1}, H_u^{−1} of non-increasing functions, never defined in the statement → the generalized inverse H^{−1}(q) = inf{x ≥ 0 : H(x) ≤ q}; min(w′, H_u^{−1}(q)) = inf({w′} ∪ {x ≥ 0 : H_u(x) ≤ q}), i.e. inf ∅ = +∞; reason: the generalized inverse F^{−1}(1 − q) := inf{v ∈ ℝ_+ : F(v) ≥ 1 − q} of §2 (p. 12) written for a non-increasing H; it is the true inverse wherever H is strictly decreasing and continuous, as for the generalized Pareto pieces used in the proof (p. App-6)
--   - encoding: ∫_w^{w′} γ s F̄(γ s) g(F̄(s)) dF(s) ≥ ∫_{q_{w′}}^{q_w} … g(q) dq → lower Lebesgue integrals ∫⁻ of ENNReal.ofReal of the integrands, over [w, w′] against μ and over [q_{w′}, q_w] against Lebesgue measure; reason: both integrands are non-negative (g ≥ 0 on [0, 1], H ∈ [0, 1], arguments ≥ 0), so ofReal changes nothing and the integrals take values in [0, ∞] without integrability side conditions; endpoints are null sets
--   - encoding: a non-negative function g : [0, 1] → ℝ_+ → g : ℝ → ℝ, measurable, with g ≥ 0 on [0, 1]; reason: the integral ∫ g(q) dq presupposes measurability; this excludes only undefined integrals
--   - encoding: non-increasing functions H : ℝ_+ → [0, 1] → H : ℝ → ℝ, antitone on [0, ∞), with H(v) ∈ [0, 1] for v ≥ 0; reason: values on negative arguments are never used
--   - encoding: a cdf F on [0, ∞) with 0 < E_F[v] < ∞ (class G, p. 11), F̄ = 1 − F → a probability measure μ on ℝ with μ((−∞, 0)) = 0, v ↦ v integrable, 0 < ∫ v dμ; F̄(p) = μ((p, ∞)); reason: same objects; F̄(p) = 1 − F(p) = P(v > p) is the strict tail
-- source:
--   Allouah, Bahamou, Besbes, Pricing with Samples, SSRN 3334650 (rev. 06/02/2021), p. 18, Lemma 1 i.)

import Mathlib
import Definitions.Def_PricingSamples_OneSampleMHR_Setting

namespace PricingSamples.OneSampleMHR

open MeasureTheory

/-- Lemma 1 i.) (p. 18): if `F̄ ≥ H_l` on `[γw, γw′]`, the revenue `v F̄(v)` is non-decreasing on
`[γw, γw′]`, and `H̃_l ≤ F̄` on `[w, w′]` with equality at `w` and `w′`, then
`∫_w^{w′} γ s F̄(γ s) g(F̄(s)) dF(s) ≥ ∫_{q_{w′}}^{q_w} γ H̃_l^{−1}(q) H_l(γ H̃_l^{−1}(q)) g(q) dq`.
Both integrands are non-negative; the integrals are lower Lebesgue integrals in `[0, ∞]`. -/
theorem lemma_1_i (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (μ : Measure ℝ) (hF : InFAlpha α μ)
    (g : ℝ → ℝ) (hg_meas : Measurable g) (hg : ∀ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g q)
    (γ w w' : ℝ) (hγ : 0 < γ) (hw : 0 ≤ w) (hww' : w < w')
    (Hl : ℝ → ℝ) (hHl_anti : AntitoneOn Hl (Set.Ici 0))
    (hHl_range : ∀ v, 0 ≤ v → Hl v ∈ Set.Icc (0 : ℝ) 1)
    (hHl : ∀ v ∈ Set.Icc (γ * w) (γ * w'), Hl v ≤ ccdf μ v)
    (hrev : MonotoneOn (fun v => v * ccdf μ v) (Set.Icc (γ * w) (γ * w')))
    (Ht : ℝ → ℝ) (hHt_anti : AntitoneOn Ht (Set.Ici 0))
    (hHt_range : ∀ v, 0 ≤ v → Ht v ∈ Set.Icc (0 : ℝ) 1)
    (hHt : ∀ v ∈ Set.Icc w w', Ht v ≤ ccdf μ v)
    (hHt_w : Ht w = ccdf μ w) (hHt_w' : Ht w' = ccdf μ w') :
    ∫⁻ q in Set.Icc (ccdf μ w') (ccdf μ w),
        ENNReal.ofReal (γ * genInv Ht q * Hl (γ * genInv Ht q) * g q) ≤
      ∫⁻ s in Set.Icc w w', ENNReal.ofReal (γ * s * ccdf μ (γ * s) * g (ccdf μ s)) ∂μ := by sorry

end PricingSamples.OneSampleMHR
