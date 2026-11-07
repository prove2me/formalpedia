-- Prove2me | Theorems.Thm_PolySampIso_fact_2
-- name    : PolySampIso.fact_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:08.27172+00:00
-- url     : https://prove2.me/theorems/7af86f51-6bac-4a37-896b-68258bdc12b7
-- title:
--   Fact 2, p.9 — relative strong convexity implies a ψ-PI ([BL76, Theorem 4.1])
-- statement:
--   Let $X\subseteq\mathbb R^d$ be open and convex, $\psi:X\to\mathbb R$ strictly convex and twice differentiable, and $\pi$ a probability measure on $X$ with Lebesgue density $e^{-U}$. If $U-\alpha\psi$ is convex on $X$ for some $\alpha>0$, i.e. $-\log\pi\succeq\alpha\psi$, then $\pi$ satisfies an $\alpha$-$\psi$-PI:
--
--   $$\mathrm{Var}_\pi[f]\le\frac1\alpha\,\mathbb E_\pi\Big[\|\nabla f\|^2_{(\nabla^2\psi)^{-1}}\Big]\quad\text{for every smooth }f.$$
--
--   This is the Brascamp–Lieb inequality in relative form. The paper uses it for $\pi_t\propto e^{-t\psi}\pi$, which satisfies a $t$-$\psi$-PI, to get the rate $\alpha_t=\max\{t,1/(16m)\}$.
--
--   Differences from the source:
--   - reading: π (a measure identified with its density, §2.1) and −log π ⪰ αψ → π = e^{−U}·Lebesgue on X with U real-valued on X, and U − αψ convex on X; reason: §2.1: a measure with a density is identified with it; f ⪰ g means f − g convex (p.7), a relation between real functions on X, so −log π is finite on X
--   - encoding: Definition 2's setting and an α-ψ-PI → X open and convex, ψ strictly convex and twice differentiable on X, α > 0; reason: strict convexity presupposes a convex domain; a PI constant is positive
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Fact 2, p.9 (PDF p.11), citing [BL76, Theorem 4.1]; ⪰ defined p.7

import Mathlib
import Definitions.Def_PolySampIso_PsiPI

open MeasureTheory ProbabilityTheory

namespace PolySampIso

/-- **Fact 2** (relative strong convexity implies a ψ-PI, [BL76, Theorem 4.1]).

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Fact 2, p.9 (PDF p.11):

"Fact 2 (Theorem 4.1, [BL76]). If −log π ⪰ αψ, then π satisfies an α-ψ-PI."
Notation, p.7: "For functions f, g, f ⪰ g means f − g is convex".

**Formalization Note.** The setting is Definition 2's: `X ⊆ ℝᵈ` open (and convex, as convexity
of functions on `X` requires), `ψ` strictly convex and twice differentiable on `X`, `π ∈ P(X)`.
`π` is identified with its density `exp(−U)` with respect to Lebesgue measure on `X` (§2.1), so
`−log π ⪰ αψ` is "`U − αψ` is convex on `X`". `α > 0` is implicit in "α-ψ-PI". -/
theorem fact_2 {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) (hXo : IsOpen X)
    (hXc : Convex ℝ X) (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (hψc : StrictConvexOn ℝ X ψ)
    (hψd : DifferentiableOn ℝ ψ X) (hψd2 : DifferentiableOn ℝ (fderiv ℝ ψ) X)
    (U : EuclideanSpace ℝ (Fin d) → ℝ) (π : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure π]
    (hπ : π = (volume.restrict X).withDensity fun x => ENNReal.ofReal (Real.exp (-U x)))
    (α : ℝ) (hα : 0 < α) (hrel : ConvexOn ℝ X fun x => U x - α * ψ x) :
    SatisfiesPsiPI π X ψ α := by sorry

end PolySampIso
