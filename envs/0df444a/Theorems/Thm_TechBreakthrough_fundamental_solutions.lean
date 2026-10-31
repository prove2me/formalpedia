-- Prove2me | Theorems.Thm_TechBreakthrough_fundamental_solutions
-- name    : TechBreakthrough.fundamental_solutions
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:49.755381+00:00
-- url     : https://prove2.me/theorems/40d4a972-fa97-4e1d-8aca-342bc818bd06
-- title:
--   §4.2 — fundamental solutions, (12), (14), (15), and the growth properties (16), (18)
-- statement:
--   Throughout, $X$ is the diffusion of §4.1 on $\mathcal I=(\alpha,\beta)$, and $R$, $G$, $f$ satisfy the standing assumptions A1–A8 of §4.2 (`Model.Valid`).
--
--   There is a fundamental pair $h_1,h_2$. For every such pair and every $c\in\mathcal I$, the ratio
--
--   $$\gamma\equiv\frac{h_1'(x)h_2(x)-h_1(x)h_2'(x)}{S'(x)}>0$$
--
--   is a constant independent of $x$. Moreover
--
--   $$\lim_{x\to\alpha^+}h_1(x)=0,\quad\lim_{x\to\beta^-}h_1(x)=\infty,\quad\lim_{x\to\alpha^+}h_2(x)=\infty,\quad\lim_{x\to\beta^-}h_2(x)=0,$$
--
--   the map $(x,y)\mapsto\mathbf E_x[e^{-r\tau(y)}]$ equals $h_1(x)/h_1(y)$ for $x\le y$ and $h_2(x)/h_2(y)$ for $x>y$, and it is continuous, and $C^2$ off the diagonal, and
--
--   $$\lim_{x\to\alpha^+}\frac{R(x)}{h_2(x)}=\lim_{x\to\beta^-}\frac{R(x)}{h_1(x)}=0,\qquad\lim_{x\to\alpha^+}\frac{G(x)}{h_2(x)}=\lim_{x\to\beta^-}\frac{G(x)}{h_1(x)}=0.$$
--
--   These classical facts, recalled by the paper, are the base of §§7–8.
--
--   Differences from the source:
--   - encoding: the diffusion solves (7) in law on the canonical space, with inaccessible (natural) endpoints −∞ ≤ α < β ≤ ∞ → laws P x on C(ℝ≥0, 𝓘); the Brownian motion lives on the canonical space; the Itô integral is the published step-approximation relation; natural means both integrals of Feller's test diverge; α, β are in EReal and limits at the ends are comap filters; reason: σ > 0 recovers the Brownian motion from X, and Feller's classification is what natural means; same instances
--   - reading: G is piecewise C² (undefined in the paper), and A7 holds everywhere G″ is defined → G is C² off a subset of 𝓘 with no accumulation point in 𝓘, with no condition on one-sided limits of G″; A7 at each x where deriv G is differentiable; reason: the weakest natural reading, hence the strongest theorem; every use in the paper goes through the concavity of Ĝ, which survives
--   - reading: the mapping (15) "is continuous and C² over {(x, y) ∈ 𝓘 × 𝓘 : x ≠ y}" → continuous on all of 𝓘 × 𝓘, and C² on {x ≠ y}; reason: the stronger reading; continuity across the diagonal holds since both formulas give 1 there
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, (12) p.10; (14)–(16) p.11; (18) p.12

import Definitions.Def_TechBreakthrough_Model_Valid
import Definitions.Def_TechBreakthrough_Model_E
import Definitions.Def_TechBreakthrough_Model_hitTransform

open MeasureTheory Filter
open scoped NNReal Topology

namespace TechBreakthrough

/-- Recalled facts of arXiv:2106.05112v1, §4.2: a fundamental pair exists (p.10), and for every
fundamental pair `h₁`, `h₂` and every `c ∈ 𝓘`: the ratio (12) is one positive constant `γ` (p.10);
the limits (14) (p.11); the hitting-time transform (15), continuous and `C²` off the diagonal
(p.11); the growth properties (16) (p.11) and (18) (p.12). -/
theorem fundamental_solutions (M : Model) (hM : M.Valid) :
    (∃ h₁ h₂, M.IsFundamentalPair h₁ h₂) ∧
    ∀ h₁ h₂, M.IsFundamentalPair h₁ h₂ →
      (∀ c ∈ M.I, 0 < M.gamma c h₁ h₂ ∧
        ∀ x ∈ M.I, M.wronskianRatio c h₁ h₂ x = M.gamma c h₁ h₂) ∧
      Tendsto h₁ M.atLeftEnd (𝓝 0) ∧ Tendsto h₁ M.atRightEnd atTop ∧
      Tendsto h₂ M.atLeftEnd atTop ∧ Tendsto h₂ M.atRightEnd (𝓝 0) ∧
      (∀ x ∈ M.I, ∀ y ∈ M.I,
        M.hitTransform x y = if x ≤ y then h₁ x / h₁ y else h₂ x / h₂ y) ∧
      ContinuousOn (Function.uncurry M.hitTransform) (M.I ×ˢ M.I) ∧
      ContDiffOn ℝ 2 (Function.uncurry M.hitTransform) {z ∈ M.I ×ˢ M.I | z.1 ≠ z.2} ∧
      Tendsto (fun x => M.R x / h₂ x) M.atLeftEnd (𝓝 0) ∧
      Tendsto (fun x => M.R x / h₁ x) M.atRightEnd (𝓝 0) ∧
      Tendsto (fun x => M.G x / h₂ x) M.atLeftEnd (𝓝 0) ∧
      Tendsto (fun x => M.G x / h₁ x) M.atRightEnd (𝓝 0) := by sorry

end TechBreakthrough
