-- Prove2me | Theorems.Thm_SinglePointPricing_Det_lemma_D_2
-- name    : SinglePointPricing.Det.lemma_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:42.922855+00:00
-- url     : https://prove2.me/theorems/5a9ffbfb-8177-4ccb-b2c0-d3a6184605c9
-- title:
--   Lemma D-2, pp. App-12–13 (corrected: right end p = 1 excluded for R_{1,α} ≤ R_{3,α}) — the crossing points p₁₃, p₁₂ in closed form and the threshold q̂_α
-- statement:
--   For $\alpha\in\{0,1\}$ and $q\in(0,1)$ let $W$ be the Lambert function on $[0,\infty)$ and $\beta_q(x) = 1-\frac{1}{\log(q^{-1})}\big(W(x)+\frac1{W(x)}-2\big)$. The crossing points of Lemma D-1 are
--   $$p_{13,0,q} = 1-\frac{(1-2q)^2}{1-q},\quad p_{12,0,q} = 1-\frac{(1-\sqrt q)^2}{1-q},\quad p_{13,1,q} = \mu_{1,q}^{-1}\Big(W\big(\tfrac1{\log(q^{-1})}\big)\Big) = \beta_q\big(\tfrac{1}{\log(q^{-1})}\big),\quad p_{12,1,q} = \mu_{1,q}^{-1}\Big(\tfrac1{W(e/q)}\Big) = \beta_q\big(\tfrac eq\big):$$
--   $p_{13,\alpha,q}\in[\underline r_\alpha(1,q),1]$ with $R_{1,\alpha}\ge R_{3,\alpha}$ on $[\underline r_\alpha(1,q),p_{13,\alpha,q}]$ and $R_{1,\alpha}\le R_{3,\alpha}$ on $[p_{13,\alpha,q},1)$ for $q\in[\underline q_\alpha,\Gamma_\alpha(\tilde v_\alpha))$, and $R_{1,\alpha}\ge R_{2,\alpha}$ on $[\underline r_\alpha(1,q),p_{12,\alpha,q}]$, $R_{1,\alpha}\le R_{2,\alpha}$ on $[p_{12,\alpha,q},1]$ for every $q\in(0,1)$.
--
--   Moreover, on $[\underline q_\alpha,\Gamma_\alpha(\tilde v_\alpha)]$ the equation $p_{13,\alpha,q} = p_{12,\alpha,q}$ has a unique solution $\hat q_\alpha$, and $p_{13,\alpha,q}\le p_{12,\alpha,q}$ if and only if $q\le\hat q_\alpha$. Here $\hat q_0 = 1/4$ and $\hat q_1 = \hat q$, the unique solution in $[0,1]$ of
--   $$W\Big(\frac1{\log(q^{-1})}\Big)\,W\Big(\frac eq\Big) = 1;\qquad \hat q\in[0.52,0.53].$$
--   (For $\alpha = 0$: $\underline q_0 = 0$, $\Gamma_0(\tilde v_0) = 1/2$; for $\alpha = 1$: $\underline q_1 = e^{-1}$, $\Gamma_1(\tilde v_1) = e^{-e^{-1}}$.)
--
--   The threshold $\hat q_\alpha$ separates the low and intermediate regimes of Theorem 2.
--
--   Differences from the source:
--   - correction: R_{1,α} ≤ R_{3,α} in [p_{13,α,q}, 1] (Lemma D-1, part 1, which defines p_{13,α,q}) → on [p_{13,α,q}, 1); reason: false at p = 1: α = 0, q = 3/10 ∈ [q̲_0, Γ_0(ṽ_0)) = [0, 1/2): R_{1,0}(1, q) = 1 > 7/10 = R_{3,0}(1, q), so no p_{13} works at p = 1 (µ_{0,q}(1) = 1 puts F_0(·|µ(1), (1, q)) in the r ≥ w branch of (3.2))
--   - reading: 'we have the following expressions' for p_{13,α,q}, p_{12,α,q} (points defined in Lemma D-1 only by their crossing property) → the closed forms are crossing points in the sense of Lemma D-1 (p_{13} on q ∈ [q̲_α, Γ_α(ṽ_α)) as in part 1, p_{12} on all q ∈ (0, 1) as in part 2), with µ_{1,q}(p_{13,1,q}) = W(1/log(q^{−1})) and µ_{1,q}(p_{12,1,q}) = 1/W(e/q) stated for the µ^{−1} expressions; reason: these are the domains on which Lemma D-1 defines the points; the proof of Theorem 2 uses p_{12,1,q} also for q < q̲_1; µ_{1,q}^{−1}(y) = 1 − (y + 1/y − 2)/log(q^{−1}) for y ∈ (0, 1] (proof, App-15–16) is β_q at the stated argument
--   - reading: q̂_α unique in [q̲_α, Γ_α(ṽ_α)] → unique in [q̲_α, Γ_α(ṽ_α)] ∩ (0, 1); reason: the paper assumes q ∈ (0, 1) throughout (p. 11); for α = 0 the closed interval contains q = 0, where p_{13,0,0} = p_{12,0,0} = 0 would be a second root
--   - encoding: W(1/log(q^{−1}))W(e/q) = 1 at q ∈ {0, 1} (undefined on the page) → Lean's log(0⁻¹) = log 0 = 0 and 1/0 = 0, so the product is W(0)·W(·) = 0 ≠ 1; reason: the endpoints are not solutions under either reading, so 'unique in [0, 1]' is stated as printed
--   - encoding: opt(F_α(·|r, (w, q))) → sup_{v ≥ 0} v F̄_α(v|r, (w, q)), computed from the ccdf (3.2); reason: (2.1) applied to the law whose ccdf on [0, ∞) is F̄_α(·|r, (w, q))
--   - reading: R_{3,0}(p, q) with r̄_0(1, q) = +∞ → (Γ_0^{−1}(q)/ṽ_0) · p Γ_0(Γ_0^{−1}(q) p); reason: at α = 0 the law F_0(·|+∞, (1, q)) is the untruncated tail Γ_0(Γ_0^{−1}(q)v), whose opt is the limit ṽ_0/Γ_0^{−1}(q) (p. App-17); for α ∈ (0, 1] R_{3,α} is encoded exactly as printed
--   - reading: Rev(p|δ_1)/Rev(1|δ_1) with F̄ = 1 − F for a right-continuous cdf F (p. 9), under which Rev(1|δ_1) = 1·P(v > 1) = 0 → R_{2,α}(p, q) = p F̄_{δ_1}(p)/(1·F̄_{δ_1}(1)) with the closed tail F̄(p) = P(v ≥ p), so R_{2,α}(p, q) = p on [0, 1]; reason: the page's revenue is ∫ p 1{v ≥ p} dF(v) = p F̄(p) (p. 9), which is the closed tail; only it makes R_{2,α} defined and equal to p, as the proof of Theorem 2 uses (R_{2,α}(p_{12,α,q}, q) = p_{12,α,q}, App-13)
-- source:
--   Allouah, Bahamou & Besbes, Optimal Pricing with a Single Point, arXiv:2103.05611v2, Lemma D-2, pp. App-12–13; Lemma D-1, parts 1–2, p. App-12

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

namespace SinglePointPricing.Det

/-- Lemma D-2, pp. App-12–13, for `α ∈ {0, 1}` and `q ∈ (0, 1)`: the closed forms
`p₁₃,₀,q = 1 − (1 − 2q)²/(1 − q)`, `p₁₂,₀,q = 1 − (1 − √q)²/(1 − q)`,
`p₁₃,₁,q = µ_{1,q}^{−1}(W(1/log(q^{−1}))) = β_q(1/log(q^{−1}))` and
`p₁₂,₁,q = µ_{1,q}^{−1}(1/W(e/q)) = β_q(e/q)` are crossing points as in Lemma D-1 (parts 1–2, with the
correction at `p = 1`); on `[q̲_α, Γ_α(ṽ_α)]` the equation `p₁₃,α,q = p₁₂,α,q` has the unique solution
`q̂_0 = 1/4`, resp. `q̂_1 = q̂`, the unique solution in `[0, 1]` of `W(1/log(q^{−1})) W(e/q) = 1`, and
`p₁₃,α,q ≤ p₁₂,α,q ↔ q ≤ q̂_α`; numerically `q̂ ∈ [0.52, 0.53]`. -/
theorem lemma_D_2 :
    ((1 / 4 : ℝ) ∈ Set.Icc (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1 ∧
      (∀ q ∈ Set.Icc (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1,
        (1 - (1 - 2 * q) ^ 2 / (1 - q) = 1 - (1 - Real.sqrt q) ^ 2 / (1 - q) ↔ q = 1 / 4) ∧
        (1 - (1 - 2 * q) ^ 2 / (1 - q) ≤ 1 - (1 - Real.sqrt q) ^ 2 / (1 - q) ↔ q ≤ 1 / 4)) ∧
      (∀ q ∈ Set.Ico (qLow 0) (GammaA 0 (vTilde 0)) ∩ Set.Ioo 0 1,
        1 - (1 - 2 * q) ^ 2 / (1 - q) ∈ Set.Icc (rLow 0 1 q) 1 ∧
        (∀ p ∈ Set.Icc (rLow 0 1 q) (1 - (1 - 2 * q) ^ 2 / (1 - q)), R3 0 q p ≤ R1 0 q p) ∧
        (∀ p ∈ Set.Ico (1 - (1 - 2 * q) ^ 2 / (1 - q)) 1, R1 0 q p ≤ R3 0 q p)) ∧
      (∀ q ∈ Set.Ioo (0 : ℝ) 1,
        (∀ p ∈ Set.Icc (rLow 0 1 q) (1 - (1 - Real.sqrt q) ^ 2 / (1 - q)), R2 p ≤ R1 0 q p) ∧
        (∀ p ∈ Set.Icc (1 - (1 - Real.sqrt q) ^ 2 / (1 - q)) 1, R1 0 q p ≤ R2 p))) ∧
    ((∃! qh : ℝ, qh ∈ Set.Icc 0 1 ∧
        lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1) ∧
      (∀ qh : ℝ, qh ∈ Set.Icc 0 1 →
        lambertW (1 / Real.log qh⁻¹) * lambertW (Real.exp 1 / qh) = 1 →
        qh ∈ Set.Icc (0.52 : ℝ) 0.53 ∧
        qh ∈ Set.Icc (qLow 1) (GammaA 1 (vTilde 1)) ∧
        ∀ q ∈ Set.Icc (qLow 1) (GammaA 1 (vTilde 1)) ∩ Set.Ioo 0 1,
          (betaQ q (1 / Real.log q⁻¹) = betaQ q (Real.exp 1 / q) ↔ q = qh) ∧
          (betaQ q (1 / Real.log q⁻¹) ≤ betaQ q (Real.exp 1 / q) ↔ q ≤ qh)) ∧
      (∀ q ∈ Set.Ico (qLow 1) (GammaA 1 (vTilde 1)) ∩ Set.Ioo 0 1,
        muAQ 1 q (betaQ q (1 / Real.log q⁻¹)) = lambertW (1 / Real.log q⁻¹) ∧
        betaQ q (1 / Real.log q⁻¹) ∈ Set.Icc (rLow 1 1 q) 1 ∧
        (∀ p ∈ Set.Icc (rLow 1 1 q) (betaQ q (1 / Real.log q⁻¹)), R3 1 q p ≤ R1 1 q p) ∧
        (∀ p ∈ Set.Ico (betaQ q (1 / Real.log q⁻¹)) 1, R1 1 q p ≤ R3 1 q p)) ∧
      (∀ q ∈ Set.Ioo (0 : ℝ) 1,
        muAQ 1 q (betaQ q (Real.exp 1 / q)) = 1 / lambertW (Real.exp 1 / q) ∧
        (∀ p ∈ Set.Icc (rLow 1 1 q) (betaQ q (Real.exp 1 / q)), R2 p ≤ R1 1 q p) ∧
        (∀ p ∈ Set.Icc (betaQ q (Real.exp 1 / q)) 1, R1 1 q p ≤ R2 p))) := by sorry

end SinglePointPricing.Det
