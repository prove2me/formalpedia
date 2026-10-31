-- Prove2me | Theorems.Thm_TechBreakthrough_lemma_6
-- name    : TechBreakthrough.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:31.097373+00:00
-- url     : https://prove2.me/theorems/0564f6a5-2f18-4862-98c2-79e5e973f4c6
-- title:
--   Lemma 6 — the nonempty compact interval $I^0$ of candidate endpoints (corrected: x_R is assumed to exist)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`). $x_R$ is a threshold of the stand-alone problem, that is $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$. $h_1,h_2$ is a pair of positive fundamental solutions of $\mathcal Lu-ru=0$ and $c\in\mathcal I$ is the base point of the scale function.
--
--   There is a nonempty compact interval $I^0=[a,a']\subset(x_R,m_{x_R})$ such that, for $m_0\in(x_R,m_{x_R})$, a candidate for the free boundary from $m_0$ exists if and only if $m_0\in I^0$. For each $m_0$ the candidate is unique on $[m_0,\beta)$.
--
--   By Lemma 5, $(x_R,m_{x_R})=\{m>x_R:E(x_R,m)>0\}$, which is the form used in Lean. The interval is later seen to be a point.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that {x ∈ 𝓘 : V_R(x) = R(x)} = [x_R, β) for some threshold x_R (p.11) → x_R is a hypothesis: x_R ∈ 𝓘 and V_R(x) = R(x) ↔ x_R ≤ x on 𝓘; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
--   - encoding: γ is the constant ratio of (12), for some fixed c ∈ 𝓘 in (13) → γ is that ratio evaluated at c, for an arbitrary c ∈ 𝓘 and an arbitrary fundamental pair; reason: fundamental_solutions shows the ratio does not depend on the point; E itself does not depend on c or on the pair
--   - encoding: b_{m₀} is the maximal solution in J_E⁺ with m_{m₀} = β, for m₀ ∈ (x_R, m_{x_R}) (p.24) → IsCandidate: E(x_R, m₀) > 0, b C¹ on [m₀, β), b(m₀) = x_R, b′ = E(b, ·), and (b(m), m) ∈ J_E with E > 0 for m > m₀; reason: J_E⁺ = E⁻¹((0, ∞)) by the page's own remark (p.24, Lemma 5 (ii)); same functions
--   - encoding: the interval (x_R, m_{x_R}) → {m₀ ∈ 𝓘 : m₀ > x_R, E(x_R, m₀) > 0}; reason: equal by Lemma 5 (ii)
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Lemma 6, p.24; b_{m₀}, p.24

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_E

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Lemma 6, arXiv:2106.05112v1, p.24: there is a nonempty compact interval
`I⁰ = [a, a′] ⊂ (x_R, m_{x_R})` such that `b_{m₀}` is a candidate for the free boundary if and only
if `m₀ ∈ I⁰`. By Lemma 5, `(x_R, m_{x_R}) = {m > x_R : E(x_R, m) > 0}`. The uniqueness of the
candidate from a given `m₀` (the page's `b_{m₀}`, p.24) is the last clause. -/
theorem lemma_6 (M : Model) (hM : M.Valid) {c : ℝ} (hc : c ∈ M.I) {h₁ h₂ : ℝ → ℝ}
    (hh : M.IsFundamentalPair h₁ h₂) {xR : ℝ} (hxR : M.IsThreshold xR) :
    (∃ a a' : ℝ, xR < a ∧ a ≤ a' ∧ a' ∈ M.I ∧ 0 < M.E c h₁ h₂ xR a ∧ 0 < M.E c h₁ h₂ xR a' ∧
      ∀ m₀ ∈ M.I, xR < m₀ → 0 < M.E c h₁ h₂ xR m₀ →
        ((∃ b, M.IsCandidate c h₁ h₂ xR m₀ b) ↔ m₀ ∈ Set.Icc a a')) ∧
    ∀ m₀ b b', M.IsCandidate c h₁ h₂ xR m₀ b → M.IsCandidate c h₁ h₂ xR m₀ b' →
      Set.EqOn b b' (M.fromLevel m₀) := by sorry

end TechBreakthrough
