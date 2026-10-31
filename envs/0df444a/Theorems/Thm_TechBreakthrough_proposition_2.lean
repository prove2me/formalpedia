-- Prove2me | Theorems.Thm_TechBreakthrough_proposition_2
-- name    : TechBreakthrough.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:20.751472+00:00
-- url     : https://prove2.me/theorems/a7ed843b-20f0-4733-8375-90a51df8ebb1
-- title:
--   §7.3, Lemma 7, Proposition 2 — candidates give solutions of (VS) (corrected: x_R is assumed to exist)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`). $x_R$ is a threshold of the stand-alone problem, that is $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$. $h_1,h_2$ is a pair of positive fundamental solutions of $\mathcal Lu-ru=0$ and $c\in\mathcal I$ is the base point of the scale function.
--
--   Let $b$ be a candidate from $\underline m$. Then $b$ is strictly increasing, the function $W_b$ of (48)–(54) lies in $\mathcal V$ (Lemma 7), and $(\underline m,b,W_b)$ is a solution to (VS). Consequently (Proposition 2) there exist $\underline m\in(x_R,\beta)$, a strictly increasing function $b\in C^1([\underline m,\beta))$ and a function $W\in\mathcal V$ such that $(\underline m,b,W)$ is a solution to (VS).
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that {x ∈ 𝓘 : V_R(x) = R(x)} = [x_R, β) for some threshold x_R (p.11) → x_R is a hypothesis: x_R ∈ 𝓘 and V_R(x) = R(x) ↔ x_R ≤ x on 𝓘; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
--   - encoding: γ is the constant ratio of (12), for some fixed c ∈ 𝓘 in (13) → γ is that ratio evaluated at c, for an arbitrary c ∈ 𝓘 and an arbitrary fundamental pair; reason: fundamental_solutions shows the ratio does not depend on the point; E itself does not depend on c or on the pair
--   - encoding: b_{m₀} is the maximal solution in J_E⁺ with m_{m₀} = β, for m₀ ∈ (x_R, m_{x_R}) (p.24) → IsCandidate: E(x_R, m₀) > 0, b C¹ on [m₀, β), b(m₀) = x_R, b′ = E(b, ·), and (b(m), m) ∈ J_E with E > 0 for m > m₀; reason: J_E⁺ = E⁻¹((0, ∞)) by the page's own remark (p.24, Lemma 5 (ii)); same functions
--   - reading: C¹ and C^{2,1} on the non-open sets J \ J_m̲, J₁, J₂, J₃, S (undefined in the paper) → derivatives along the horizontal and vertical slices of the set, with continuous extensions to the set; reason: this is what the proof of Lemma 7 checks, and the paper's W satisfies it at the diagonal and on x = b(m)
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, §7.3, pp.25–27; Lemma 7, p.27; Proposition 2, p.20

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_IsSolution
import Definitions.Def_TechBreakthrough_Model_Wb

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- §7.3, Lemma 7 and Proposition 2, arXiv:2106.05112v1, pp.25–27 and p.20: every candidate `b` from
`m̲` is strictly increasing, and the function `W_b` of (48)–(54) lies in `𝒱` and makes
`(m̲, b, W_b)` a solution of (VS). Consequently there exist `m̲ ∈ (x_R, β)`, a strictly increasing
`b ∈ C¹([m̲, β))` and `W ∈ 𝒱` such that `(m̲, b, W)` is a solution to (VS). -/
theorem proposition_2 (M : Model) (hM : M.Valid) {c : ℝ} (hc : c ∈ M.I) {h₁ h₂ : ℝ → ℝ}
    (hh : M.IsFundamentalPair h₁ h₂) {xR : ℝ} (hxR : M.IsThreshold xR) :
    (∀ mLow b, M.IsCandidate c h₁ h₂ xR mLow b →
      StrictMonoOn b (M.fromLevel mLow) ∧
      M.IsSolution xR mLow b (M.Wb c h₁ h₂ xR mLow b)) ∧
    ∃ mLow b W, M.IsSolution xR mLow b W ∧ StrictMonoOn b (M.fromLevel mLow) := by sorry

end TechBreakthrough
