-- Prove2me | Theorems.Thm_StochasticProg_RecourseKKT_theorem_9
-- name    : StochasticProg.RecourseKKT.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:54:40.180821+00:00
-- url     : https://prove2.me/theorems/a9d051f5-7517-43d0-8274-d8fca519a0ef
-- title:
--   Theorem 9 — Karush–Kuhn–Tucker conditions for two-stage stochastic linear programs (corrected: regularity condition on the only-if direction)
-- statement:
--   Consider a two-stage stochastic linear program with fixed recourse on a probability space $(\Omega, \mathcal F, P)$, with deterministic equivalent (1.2): minimize $c^{\mathsf T}x + \mathcal Q(x)$ over $K_1 = \{x \mid Ax = b,\ x \ge 0\}$. Assume that
--
--   1. $\xi = (q, h, T)$ has finite second moments,
--   2. $Q(x,\xi) \ne -\infty$ for every $x$, almost surely, and
--   3. (1.2) has a finite optimal value.
--
--   Let $x^* \in K_1$, and consider the condition: there exist $\lambda^* \in \mathbb R^{m_1}$ and $\mu^* \in \mathbb R^{n_1}$ with $\mu^* \ge 0$ and $\mu^{*\mathsf T}x^* = 0$ such that
--
--   $$
--   -c + A^{\mathsf T} \lambda^* + \mu^* \in \partial \mathcal Q(x^*). \tag{1.12}
--   $$
--
--   - **(if)** If (1.12) holds, then $x^*$ is optimal in (1.2).
--   - **(only if, corrected)** Assume moreover the regularity condition
--     (R) $K_1 \cap \operatorname{ri} K_2 \ne \emptyset$, or $K_2$ is a convex polyhedron, or $K_1 \subseteq K_2$ (relatively complete recourse). If $x^*$ is optimal in (1.2), then (1.12) holds.
--
--   Theorem 9 is the Karush–Kuhn–Tucker characterization of optimal first-stage decisions; (1.12) is the inclusion on which subgradient methods for (1.2) rest, and Corollaries 10 and 12 specialize it to simple and to relatively complete recourse.
--
--   The book states the equivalence without (R). Its "only if" direction is false as printed: with $n_1 = 2$, $A = [1\ 0]$, $b = 0$ (so $K_1 = \{(0, s) \mid s \ge 0\}$), $c = (0, 1)$, $W = [1]$, $q \equiv 0$, $\theta$ uniform on $[0, 2\pi)$, $T(\theta) = [\cos\theta,\ \sin\theta]$ and $h(\theta) = \cos\theta + \sin\theta + 1$, every assumption holds, $K_2$ is the closed disc of centre $(1,1)$ and radius $1$, and $x^* = (0, 1)$ is optimal, but (1.12) would require $\mu^*_2 = 1$ and $\mu^*_2 = \mu^{*\mathsf T}x^* = 0$. Each case of (R) is one the book uses: finite $\xi$ (Theorem 1(b)), fixed $T$ (Theorem 5(b)), relatively complete recourse (Corollary 12).
--
--   **Formalization Note** $\mathcal Q$ is valued in the extended reals with $+\infty + (-\infty) = +\infty$; $\partial \mathcal Q(x^*)$ is empty where $\mathcal Q(x^*)$ is infinite; $\operatorname{ri}$ is the relative interior.
--
--   Differences from the source:
--   - correction: x* optimal in (1.2) ⇒ (1.12), with no further condition → the 'only if' direction assumes (R): K₁ ∩ ri K₂ ≠ ∅, or K₂ polyhedral, or K₁ ⊆ K₂; reason: false as printed. Counterexample satisfying every assumption of the book: n1 = 2, A = [1 0], b = 0 (K₁ = {(0, s) | s ≥ 0}), c = (0, 1), W = [1], q ≡ 0, θ uniform on [0, 2π), T(θ) = [cos θ, sin θ], h(θ) = cos θ + sin θ + 1: K₂ is the closed disc of centre (1, 1) and radius 1, x* = (0, 1) is optimal with value 1, ∂𝒬(x*) = {(−t, 0) | t ≥ 0}; (1.12) would need μ₂ = 1 and μ₂ = μᵀx* = 0
--   - generalization: Q(x, ξ) is not −∞ (for every x and ξ, p. 112) → for every x, Q(x, ξ(ω)) ≠ −∞ for P-almost every ω; reason: a weaker hypothesis, implied by the book's; null events do not affect 𝒬 (p. 110)
--   - encoding: ξ has finite second moments → every coordinate of q, h, T is in L²(P); reason: equivalent to E‖ξ‖² < ∞
--   - encoding: ∂f(x) = {η | f(w) ≥ f(x) + ηᵀ(w − x) ∀w} → subdifferential with f(x) required real (empty where f(x) = ±∞); reason: the convex-analysis convention for extended-valued functions; at points where 𝒬 is finite it is the book's set
--   - encoding: 𝒬(x) = E_ξ Q(x, ξ) with +∞ + (−∞) = +∞ and 0·∞ = 0 → EReal value: +∞ if ∫⁻ Q⁺ = ∞, else ∫⁻ Q⁺ − ∫⁻ Q⁻; reason: the book's convention written out; same instances
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, Theorem 9, printed p. 116 (PDF p. 141), with the standing assumptions of printed pp. 109, 112, 115

import Mathlib
import Definitions.Def_StochasticProg_RecourseKKT_RecourseData
import Definitions.Def_StochasticProg_RecourseKKT_expectedRecourse
import Definitions.Def_StochasticProg_RecourseKKT_firstStageSet
import Definitions.Def_StochasticProg_RecourseKKT_secondStageFeasSet
import Definitions.Def_StochasticProg_RecourseKKT_IsOptimalDEP
import Definitions.Def_StochasticProg_RecourseKKT_HasFiniteOptimalValue
import Definitions.Def_StochasticProg_RecourseKKT_FiniteSecondMoments
import Definitions.Def_StochasticProg_RecourseKKT_RecourseNotNegInf
import Definitions.Def_StochasticProg_RecourseKKT_subdifferential
import Definitions.Def_StochasticProg_RecourseKKT_IsPolyhedralSet
open MeasureTheory Matrix

namespace StochasticProg.RecourseKKT

/-- **Theorem 9 (Karush–Kuhn–Tucker conditions for the deterministic equivalent), corrected.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, Chapter 3, §3.1e, Theorem 9, printed p. 116 (PDF p. 141), under the standing assumptions of
pp. 109, 112, 115 (fixed recourse; `Q(x, ξ)` not `−∞`; `ξ` with finite second moments):
"Suppose (1.2) has a finite optimal value. A solution x* ∈ K₁, is optimal in (1.2) if and only if
there exists some λ* ∈ ℜ^{m1}, μ* ∈ ℜ^{n1}_+, μ*ᵀx* = 0, such that, −c + Aᵀλ* + μ* ∈ ∂𝒬(x*). (1.12)"

Let `ξ` have finite second moments, `Q(x, ξ) ≠ −∞`, and suppose (1.2) has a finite optimal value.
For `x* ∈ K₁`:
(i) if (1.12) holds for some `λ*`, `μ* ≥ 0` with `μ*ᵀx* = 0`, then `x*` is optimal in (1.2);
(ii) **(corrected)** if the regularity condition (R) holds — `K₁ ∩ ri K₂ ≠ ∅`, or `K₂` is a convex
polyhedron, or `K₁ ⊆ K₂` (relatively complete recourse) — and `x*` is optimal in (1.2), then such
`λ*`, `μ*` exist.

**Formalization Note (correction).** The printed "only if" is false. Counterexample satisfying every
assumption of the book: `n1 = 2`, `m1 = 1`, `A = [1 0]`, `b = 0` (so `K₁ = {(0, s) | s ≥ 0}`),
`c = (0, 1)`, `m2 = n2 = 1`, `W = [1]`, `q ≡ 0`, `θ` uniform on `[0, 2π)`, `T(θ) = [cos θ, sin θ]`,
`h(θ) = cos θ + sin θ + 1`. Then `𝒬 = 0` on the closed disc of centre `(1, 1)` and radius `1` and
`+∞` off it, `x* = (0, 1)` is optimal with value `1`, `∂𝒬(x*) = {(−t, 0) | t ≥ 0}`, and (1.12)
would need `μ₂ = 1` and `μ₂ = μᵀx* = 0`. (R) is assumed on the "only if" direction only.
`𝒬` is `expectedRecourse` (`EReal`, `+∞ + (−∞) = +∞`), `∂` is `subdifferential` (empty where the
function is infinite), `ri` is `intrinsicInterior`, `0 ≤ μ` is componentwise. -/
theorem theorem_9 {Ω : Type*} [MeasurableSpace Ω] {n1 m1 n2 m2 : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (pb : RecourseData Ω n1 m1 n2 m2)
    (hmom : FiniteSecondMoments P pb) (hnn : RecourseNotNegInf P pb)
    (hfin : HasFiniteOptimalValue P pb)
    (xs : Fin n1 → ℝ) (hxs : xs ∈ firstStageSet pb.A pb.b) :
    ((∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
          -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) →
        IsOptimalDEP P pb xs) ∧
      (((firstStageSet pb.A pb.b ∩ intrinsicInterior ℝ (secondStageFeasSet P pb)).Nonempty ∨
          IsPolyhedralSet (secondStageFeasSet P pb) ∨
          firstStageSet pb.A pb.b ⊆ secondStageFeasSet P pb) →
        IsOptimalDEP P pb xs →
          ∃ (lam : Fin m1 → ℝ) (mu : Fin n1 → ℝ), 0 ≤ mu ∧ mu ⬝ᵥ xs = 0 ∧
            -pb.c + pb.Aᵀ *ᵥ lam + mu ∈ subdifferential (expectedRecourse P pb) xs) := by sorry

end StochasticProg.RecourseKKT
