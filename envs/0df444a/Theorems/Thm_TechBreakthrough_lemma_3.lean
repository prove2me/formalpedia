-- Prove2me | Theorems.Thm_TechBreakthrough_lemma_3
-- name    : TechBreakthrough.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:59.465553+00:00
-- url     : https://prove2.me/theorems/e296b560-9dc6-4108-a7d6-d9a5a2e4d006
-- title:
--   Lemma 3 — $E\to\infty$ at the diagonal (corrected: x_R is assumed to exist)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`). $x_R$ is a threshold of the stand-alone problem, that is $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$. $h_1,h_2$ is a pair of positive fundamental solutions of $\mathcal Lu-ru=0$ and $c\in\mathcal I$ is the base point of the scale function.
--
--   For each $m\in[x_R,\beta)$,
--
--   $$\lim_{(x,m'),\,x<m'\to(m,m)}E(x,m')=\infty.$$
--
--   So the vector field of the free-boundary ODE has no continuous extension to the diagonal: the singularity that keeps the free boundary strictly below it.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that {x ∈ 𝓘 : V_R(x) = R(x)} = [x_R, β) for some threshold x_R (p.11) → x_R is a hypothesis: x_R ∈ 𝓘 and V_R(x) = R(x) ↔ x_R ≤ x on 𝓘; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
--   - encoding: γ is the constant ratio of (12), for some fixed c ∈ 𝓘 in (13) → γ is that ratio evaluated at c, for an arbitrary c ∈ 𝓘 and an arbitrary fundamental pair; reason: fundamental_solutions shows the ratio does not depend on the point; E itself does not depend on c or on the pair
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Lemma 3 (37), p.21; proof p.40

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_E

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Lemma 3, (37), arXiv:2106.05112v1, p.21 (proof p.40): for each `m ∈ [x_R, β)`,
`E(x, m′) → ∞` as `(x, m′) → (m, m)` with `x < m′`, within `J_E`. -/
theorem lemma_3 (M : Model) (hM : M.Valid) {c : ℝ} (hc : c ∈ M.I) {h₁ h₂ : ℝ → ℝ}
    (hh : M.IsFundamentalPair h₁ h₂) {xR : ℝ} (hxR : M.IsThreshold xR) :
    ∀ m ∈ M.fromLevel xR,
      Tendsto (fun z : ℝ × ℝ => M.E c h₁ h₂ z.1 z.2) (𝓝[M.domainE xR] (m, m)) atTop := by sorry

end TechBreakthrough
