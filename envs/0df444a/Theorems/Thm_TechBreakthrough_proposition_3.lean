-- Prove2me | Theorems.Thm_TechBreakthrough_proposition_3
-- name    : TechBreakthrough.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:38:12.809664+00:00
-- url     : https://prove2.me/theorems/975ac4e1-7f80-41ff-a142-41180dc2c516
-- title:
--   Proposition 3 — $V=W=V_b$ (corrected: x_R is assumed to exist)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`). $x_R$ is a threshold of the stand-alone problem, that is $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$.
--
--   Let $(\underline m,b,W)$ be any solution of (VS) in the class of Theorem 1. For all $(x,m)\in J$, $W(x,m)$ is the least upper bound of the expected rewards of (19), hence $V(x,m)=W(x,m)$, and $W(x,m)=V_b(x,m)$, the expected reward at $\tau_b$.
--
--   It concludes the proof of Theorem 1: since $V$ is unique, so are $W$ and $b$.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that {x ∈ 𝓘 : V_R(x) = R(x)} = [x_R, β) for some threshold x_R (p.11) → x_R is a hypothesis: x_R ∈ 𝓘 and V_R(x) = R(x) ↔ x_R ≤ x on 𝓘; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
--   - encoding: stopping times in T_{X,M} and expectation E_{x,m} under the law of (X, M) → stopping times in T_X under P x, with M = runningMax m a function of the path; reason: p.13: every element of T_{X,M} is P_{x,m}-a.s. in T_X, and M is a function of X and m; same values
--   - encoding: the Stieltjes integral ∫_0^τ … dM_t → the integral over (0, τ], or (0, ∞) when τ = ∞, against the Stieltjes measure of t ↦ M_{t∨0}; reason: M is continuous and nondecreasing, so the measure has no atoms; same value
--   - reading: C¹ and C^{2,1} on the non-open sets J \ J_m̲, J₁, J₂, J₃, S (undefined in the paper) → derivatives along the horizontal and vertical slices of the set, with continuous extensions to the set; reason: this is what the proof of Lemma 7 checks, and the paper's W satisfies it at the diagonal and on x = b(m)
--   - generalization: Proposition 3 is stated for the solution built from a fixed candidate b (§8, p.27) → it holds for every solution of (VS) in the class of Theorem 1; reason: specializes to the page by proposition_2; the page's uniqueness argument (pp.21, 23, 27–28) uses this form
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Proposition 3, p.28; (55), p.27

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_IsSolution
import Definitions.Def_TechBreakthrough_Model_tauB

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Proposition 3, arXiv:2106.05112v1, p.28: `V = W = V_b`, for every solution `(m̲, b, W)` of (VS) in
the class of Theorem 1: on `J`, `W` is the least upper bound of the expected rewards of (19), so
`V = W`, and `τ_b` attains it.

**Formalization Note** The page fixes the solution built from a candidate (§8, p.27) and derives
uniqueness from this result (p.28); stating it for every solution in the class is what that
derivation uses (pp.21, 23, 27–28). -/
theorem proposition_3 (M : Model) (hM : M.Valid) {xR : ℝ} (hxR : M.IsThreshold xR)
    {mLow : ℝ} {b : ℝ → ℝ} {W : ℝ → ℝ → ℝ} (hsol : M.IsSolution xR mLow b W) :
    ∀ z ∈ M.domain,
      IsLUB (M.valueSet z.1 z.2) (W z.1 z.2) ∧ M.V z.1 z.2 = W z.1 z.2 ∧
      W z.1 z.2 = ∫ ω, M.payoff z.2 (M.tauB xR mLow b z.2) ω ∂M.P z.1 := by sorry

end TechBreakthrough
