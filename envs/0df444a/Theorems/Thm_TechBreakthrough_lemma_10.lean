-- Prove2me | Theorems.Thm_TechBreakthrough_lemma_10
-- name    : TechBreakthrough.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:48.637194+00:00
-- url     : https://prove2.me/theorems/04b07c91-f6a1-4989-be5e-26fd1c0c3e6d
-- title:
--   Lemma 10 — $W$ is superharmonic (corrected: x_R is assumed to exist)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`). $x_R$ is a threshold of the stand-alone problem, that is $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$. $h_1,h_2$ is a pair of positive fundamental solutions of $\mathcal Lu-ru=0$ and $c\in\mathcal I$ is the base point of the scale function. $b$ is a candidate for the free boundary from $\underline m$, and $W=W_b$ is the function of (48)–(54).
--
--   For all stopping times $\tau$ and $(x,m)\in J$,
--
--   $$W(x,m)\ge\mathbf E_{x,m}\Big[e^{-r\tau}W(X_\tau,M_\tau)+\int_0^\tau e^{-rt}G(M_t)f(M_t)\,dM_t\Big].$$
--
--   With Lemma 8, this gives $V\le W$.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that {x ∈ 𝓘 : V_R(x) = R(x)} = [x_R, β) for some threshold x_R (p.11) → x_R is a hypothesis: x_R ∈ 𝓘 and V_R(x) = R(x) ↔ x_R ≤ x on 𝓘; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
--   - encoding: γ is the constant ratio of (12), for some fixed c ∈ 𝓘 in (13) → γ is that ratio evaluated at c, for an arbitrary c ∈ 𝓘 and an arbitrary fundamental pair; reason: fundamental_solutions shows the ratio does not depend on the point; E itself does not depend on c or on the pair
--   - encoding: b_{m₀} is the maximal solution in J_E⁺ with m_{m₀} = β, for m₀ ∈ (x_R, m_{x_R}) (p.24) → IsCandidate: E(x_R, m₀) > 0, b C¹ on [m₀, β), b(m₀) = x_R, b′ = E(b, ·), and (b(m), m) ∈ J_E with E > 0 for m > m₀; reason: J_E⁺ = E⁻¹((0, ∞)) by the page's own remark (p.24, Lemma 5 (ii)); same functions
--   - encoding: stopping times in T_{X,M} and expectation E_{x,m} under the law of (X, M) → stopping times in T_X under P x, with M = runningMax m a function of the path; reason: p.13: every element of T_{X,M} is P_{x,m}-a.s. in T_X, and M is a function of X and m; same values
--   - encoding: the Stieltjes integral ∫_0^τ … dM_t → the integral over (0, τ], or (0, ∞) when τ = ∞, against the Stieltjes measure of t ↦ M_{t∨0}; reason: M is continuous and nondecreasing, so the measure has no atoms; same value
--   - encoding: "τ ∈ T_{x,m}" (typo on p.32) → τ ∈ T_X; reason: the page means T_{X,M}, see p.20; same set by the entry above
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Lemma 10 (63), p.32

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_stopRegion
import Definitions.Def_TechBreakthrough_Model_Wb

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Lemma 10, (63), arXiv:2106.05112v1, p.32: for all `τ ∈ T_X` and `(x, m) ∈ J`,
`W(x, m) ≥ E_{x,m}[e^{−rτ} W(X_τ, M_τ) + ∫_0^τ e^{−rt} G(M_t) f(M_t) dM_t]`. Here `W = W_b` for a
candidate `b`, and `e^{−rτ} W(X_τ, M_τ) = 0` on `{τ = ∞}`. -/
theorem lemma_10 (M : Model) (hM : M.Valid) {c : ℝ} (hc : c ∈ M.I) {h₁ h₂ : ℝ → ℝ}
    (hh : M.IsFundamentalPair h₁ h₂) {xR : ℝ} (hxR : M.IsThreshold xR)
    {mLow : ℝ} {b : ℝ → ℝ} (hb : M.IsCandidate c h₁ h₂ xR mLow b) :
    ∀ τ ∈ M.T, ∀ z ∈ M.domain,
      ∫ ω, (discountedAt M.r
          (fun t => M.Wb c h₁ h₂ xR mLow b (M.X t ω) (runningMax z.2 t ω)) (τ ω) +
        ∫ t in Model.elapsed (τ ω), M.flow z.2 ω t ∂(dMax z.2 ω)) ∂M.P z.1 ≤
      M.Wb c h₁ h₂ xR mLow b z.1 z.2 := by sorry

end TechBreakthrough
