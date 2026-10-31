-- Prove2me | Theorems.Thm_TechBreakthrough_theorem_1
-- name    : TechBreakthrough.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:50.420523+00:00
-- url     : https://prove2.me/theorems/54988644-ec76-456b-980b-2d66ce2eac16
-- title:
--   Theorem 1 — (VS) has a unique solution; $b$ is strictly increasing, $W=V$, and $\tau_b$ is optimal (corrected: x_R is assumed to exist)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`). $x_R$ is a threshold of the stand-alone problem, that is $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$.
--
--   (VS) admits a unique solution $(\underline m,b,W)$ in $(x_R,\beta)\times C^1([\underline m,\beta))\times\mathcal V$, where
--
--   $$\mathcal V\equiv C^0(J)\cap C^1(J\setminus J_{\underline m})\cap C^{2,1}(J_1)\cap C^{2,1}(J_2)\cap C^{2,1}(J_3)\cap C^{2,1}(S).$$
--
--   Moreover:
--
--   1. the function $b$ is strictly increasing;
--   2. the function $W$ coincides with the value function $V$ of problem (19);
--   3. the stopping time $\tau_b\equiv\inf\{t\ge0:M_t\ge\underline m\text{ and }x_R\le X_t\le b(M_t)\}$ is optimal for problem (19), that is,
--
--   $$V(x,m)=\mathbf E_{x,m}\Big[[1-F(M_{\tau_b})]e^{-r\tau_b}R(X_{\tau_b})+\int_0^{\tau_b}e^{-rt}G(M_t)f(M_t)\,dM_t\Big]$$
--
--   for all $(x,m)\in J$.
--
--   This solves the investment problem completely: it is optimal to invest in the stand-alone technology as soon as the running maximum is at least $\underline m$ and $X$ has fallen to the interval $[x_R,b(M)]$.
--
--   **Formalization Note** Uniqueness is in the paper's class: $\underline m$ is unique, $b$ on $[\underline m,\beta)$, and $W$ on $J$. The solution predicate does not include strict monotonicity of $b$. Clause 2 gives $W$ as a least upper bound, so the real supremum defining $V$ is not a junk value. $\tau_b$ is an element of $T_X$ for each starting level $m\in\mathcal I$, and it may be infinite.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that {x ∈ 𝓘 : V_R(x) = R(x)} = [x_R, β) for some threshold x_R (p.11) → x_R is a hypothesis: x_R ∈ 𝓘 and V_R(x) = R(x) ↔ x_R ≤ x on 𝓘; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
--   - encoding: stopping times in T_{X,M} and expectation E_{x,m} under the law of (X, M) → stopping times in T_X under P x, with M = runningMax m a function of the path; reason: p.13: every element of T_{X,M} is P_{x,m}-a.s. in T_X, and M is a function of X and m; same values
--   - encoding: the Stieltjes integral ∫_0^τ … dM_t → the integral over (0, τ], or (0, ∞) when τ = ∞, against the Stieltjes measure of t ↦ M_{t∨0}; reason: M is continuous and nondecreasing, so the measure has no atoms; same value
--   - reading: C¹ and C^{2,1} on the non-open sets J \ J_m̲, J₁, J₂, J₃, S (undefined in the paper) → derivatives along the horizontal and vertical slices of the set, with continuous extensions to the set; reason: this is what the proof of Lemma 7 checks, and the paper's W satisfies it at the diagonal and on x = b(m)
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Theorem 1, pp.18–19

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_IsSolution
import Definitions.Def_TechBreakthrough_Model_tauB

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Theorem 1, arXiv:2106.05112v1, pp.18–19. (VS) admits a unique solution `(m̲, b, W)` in
`(x_R, β) × C¹([m̲, β)) × 𝒱`. Moreover, (i) `b` is strictly increasing; (ii) `W` coincides with
the value function `V` of problem (19); (iii) the stopping time
`τ_b = inf {t ≥ 0 : M_t ≥ m̲ and x_R ≤ X_t ≤ b(M_t)}` is optimal for problem (19).

**Correction.** The page's `x_R` need not exist (p.11; see `TechBreakthrough.lemma_1`), so the
theorem is stated for every threshold `x_R` of the stand-alone problem.

**Formalization Note** Uniqueness is in the page's class: `m̲`, then `b` on `[m̲, β)`, `W` on `J`.
`IsSolution` does not include strict monotonicity of `b`. Clause (ii) gives `IsLUB`, so the
real supremum defining `V` is not a junk value. In (iii), `τ_b` depends on the starting level `m`
of `M`, is an element of `T_X`, and may be infinite. -/
theorem theorem_1 (M : Model) (hM : M.Valid) {xR : ℝ} (hxR : M.IsThreshold xR) :
    ∃ (mLow : ℝ) (b : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      M.IsSolution xR mLow b W ∧
      (∀ (mLow' : ℝ) (b' : ℝ → ℝ) (W' : ℝ → ℝ → ℝ), M.IsSolution xR mLow' b' W' →
        mLow' = mLow ∧ Set.EqOn b' b (M.fromLevel mLow) ∧
        Set.EqOn (Function.uncurry W') (Function.uncurry W) M.domain) ∧
      StrictMonoOn b (M.fromLevel mLow) ∧
      (∀ z ∈ M.domain, IsLUB (M.valueSet z.1 z.2) (W z.1 z.2) ∧ M.V z.1 z.2 = W z.1 z.2) ∧
      (∀ m ∈ M.I, M.tauB xR mLow b m ∈ M.T) ∧
      (∀ z ∈ M.domain,
        M.V z.1 z.2 = ∫ ω, M.payoff z.2 (M.tauB xR mLow b z.2) ω ∂M.P z.1) := by sorry

end TechBreakthrough
