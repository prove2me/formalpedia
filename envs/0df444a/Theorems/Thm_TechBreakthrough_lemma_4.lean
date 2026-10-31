-- Prove2me | Theorems.Thm_TechBreakthrough_lemma_4
-- name    : TechBreakthrough.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:37:21.111264+00:00
-- url     : https://prove2.me/theorems/c304a9ca-02b3-4810-81be-25cac45047b9
-- title:
--   Lemma 4 — the free boundary solves the ODE $b^\prime=E(b,\cdot)$ (corrected: x_R is assumed to exist)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`). $x_R$ is a threshold of the stand-alone problem, that is $\{x\in\mathcal I:V_R(x)=R(x)\}=[x_R,\beta)$. $h_1,h_2$ is a pair of positive fundamental solutions of $\mathcal Lu-ru=0$ and $c\in\mathcal I$ is the base point of the scale function.
--
--   If $(\underline m,b,W)$ is a solution to (VS) with $b\in C^1([\underline m,\beta))$ and $W\in\mathcal V$, then
--
--   $$b'(m)=E(b(m),m),\quad m\in[\underline m,\beta),\qquad b(\underline m)=x_R.$$
--
--   At $\underline m$ the derivative is the right derivative. This narrows the candidates for the free boundary to solutions of one ODE.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - correction: A3 guarantees that {x ∈ 𝓘 : V_R(x) = R(x)} = [x_R, β) for some threshold x_R (p.11) → x_R is a hypothesis: x_R ∈ 𝓘 and V_R(x) = R(x) ↔ x_R ≤ x on 𝓘; reason: false as printed: geometric Brownian motion dX = √2 X dW, r = 2, R(x) = −x²/(1 + x⁶), G(x) = √x, f(y) = e^{−y} satisfies A1–A8 with V_R ≡ 0 and {V_R = R} = ∅; such an x_R exists exactly when R > 0 somewhere (lemma_1)
--   - encoding: γ is the constant ratio of (12), for some fixed c ∈ 𝓘 in (13) → γ is that ratio evaluated at c, for an arbitrary c ∈ 𝓘 and an arbitrary fundamental pair; reason: fundamental_solutions shows the ratio does not depend on the point; E itself does not depend on c or on the pair
--   - reading: C¹ and C^{2,1} on the non-open sets J \ J_m̲, J₁, J₂, J₃, S (undefined in the paper) → derivatives along the horizontal and vertical slices of the set, with continuous extensions to the set; reason: this is what the proof of Lemma 7 checks, and the paper's W satisfies it at the diagonal and on x = b(m)
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, Lemma 4, (38)–(39), p.21; proof pp.40–42

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_E
import Definitions.Def_TechBreakthrough_Model_IsSolution

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Lemma 4, arXiv:2106.05112v1, p.21 (proof pp.40–42): if `(m̲, b, W)` is a solution to (VS) with
`b ∈ C¹([m̲, β))` and `W ∈ 𝒱`, then `b′(m) = E(b(m), m)` on `[m̲, β)`, which is (38), and
`b(m̲) = x_R`, which is (39).

**Formalization Note** The derivative is taken within `[m̲, β)`: it is the right derivative at
`m̲`, and two-sided elsewhere. -/
theorem lemma_4 (M : Model) (hM : M.Valid) {c : ℝ} (hc : c ∈ M.I) {h₁ h₂ : ℝ → ℝ}
    (hh : M.IsFundamentalPair h₁ h₂) {xR : ℝ} (hxR : M.IsThreshold xR)
    {mLow : ℝ} {b : ℝ → ℝ} {W : ℝ → ℝ → ℝ} (hsol : M.IsSolution xR mLow b W) :
    (∀ m ∈ M.fromLevel mLow,
      HasDerivWithinAt b (M.E c h₁ h₂ (b m) m) (M.fromLevel mLow) m) ∧
    b mLow = xR := by sorry

end TechBreakthrough
