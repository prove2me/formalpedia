-- Prove2me | Theorems.Thm_TechBreakthrough_lemma_5
-- name    : TechBreakthrough.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:15.035012+00:00
-- url     : https://prove2.me/theorems/0bf48479-bcc2-47ac-8e79-833fc4ea3f75
-- title:
--   Lemma 5 — the zero curve $m=m_x$ of $E$ (corrected: x_R is assumed to exist)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`). $x_R$ is a threshold of the stand-alone problem, that is $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$. $h_1,h_2$ is a pair of positive fundamental solutions of $\mathcal Lu-ru=0$ and $c\in\mathcal I$ is the base point of the scale function.
--
--   There is a strictly increasing $C^1$ mapping $x\mapsto m_x$ over $[x_R,\beta)$ such that
--
--   1. for each $x\in[x_R,\beta)$, $m_x>x$;
--   2. for each $(x,m)\in J_E$, $E(x,m_x)=0$, and $E(x,m)\lessgtr0$ if $m\gtrless m_x$;
--   3. $\lim_{x\to\beta^-}m_x=\beta$.
--
--   Geometrically, the vector field points to the left above an increasing curve. Together with the diagonal, this curve bounds the region where a free boundary can live.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that {x ∈ 𝓘 : V_R(x) = R(x)} = [x_R, β) for some threshold x_R (p.11) → x_R is a hypothesis: x_R ∈ 𝓘 and V_R(x) = R(x) ↔ x_R ≤ x on 𝓘; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
--   - encoding: γ is the constant ratio of (12), for some fixed c ∈ 𝓘 in (13) → γ is that ratio evaluated at c, for an arbitrary c ∈ 𝓘 and an arbitrary fundamental pair; reason: fundamental_solutions shows the ratio does not depend on the point; E itself does not depend on c or on the pair
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Lemma 5, p.22

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_E

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Lemma 5, arXiv:2106.05112v1, p.22: there is a strictly increasing `C¹` mapping `x ↦ m_x` over
`[x_R, β)` such that (i) `m_x > x`; (ii) for each `(x, m) ∈ J_E`, `E(x, m_x) = 0` and
`E(x, m) ≶ 0` if `m ≷ m_x`; (iii) `m_x → β` as `x → β⁻`. -/
theorem lemma_5 (M : Model) (hM : M.Valid) {c : ℝ} (hc : c ∈ M.I) {h₁ h₂ : ℝ → ℝ}
    (hh : M.IsFundamentalPair h₁ h₂) {xR : ℝ} (hxR : M.IsThreshold xR) :
    ∃ mx : ℝ → ℝ, ContDiffOn ℝ 1 mx (M.fromLevel xR) ∧ StrictMonoOn mx (M.fromLevel xR) ∧
      (∀ x ∈ M.fromLevel xR, mx x ∈ M.I ∧ x < mx x ∧ M.E c h₁ h₂ x (mx x) = 0) ∧
      (∀ z ∈ M.domainE xR,
        (mx z.1 < z.2 → M.E c h₁ h₂ z.1 z.2 < 0) ∧ (z.2 < mx z.1 → 0 < M.E c h₁ h₂ z.1 z.2)) ∧
      Tendsto (fun x => (mx x : EReal)) M.atRightEnd (𝓝 M.β) := by sorry

end TechBreakthrough
