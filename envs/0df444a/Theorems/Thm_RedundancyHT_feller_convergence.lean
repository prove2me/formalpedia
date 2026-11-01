-- Prove2me | Theorems.Thm_RedundancyHT_feller_convergence
-- name    : RedundancyHT.feller_convergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:24:40.264979+00:00
-- url     : https://prove2.me/theorems/814d23a6-f64a-4488-98c2-4f0a3fdfae9d
-- title:
--   Feller's convergence theorem, p.18: pointwise convergence of transforms on the orthant gives convergence in distribution
-- statement:
--   Let $\nu$ and $\mu_a$ be probability measures on the non-negative orthant of $\mathbb R^n$, the latter eventually along a filter $l$. If
--   $$\int e^{-\langle t,x\rangle}\,\mu_a(dx)\longrightarrow\int e^{-\langle t,x\rangle}\,\nu(dx)\qquad\text{for every }t\ge0,$$
--   then $\mu_a$ converges in distribution to $\nu$ along $l$.
--
--   The paper uses this classical result from Feller for the families indexed by $\lambda\uparrow\lambda^*$.
--
--   Differences from the source:
--   - generalization: the random vector (1 − λ/λ*)(Q_S) as λ ↑ λ* → arbitrary probability measures on the orthant along an arbitrary filter; reason: the family of the paper along 𝓝[<] λ* is the special case
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §4, p.18, sentence beginning "By Feller's Convergence Theorem [22]"; repeated on p.32 (the paper cites Feller [22])

import Definitions.Def_RedundancyHT_ConvergesInLaw
import Definitions.Def_RedundancyHT_laplace

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **Feller's convergence theorem as used on p.18** (arXiv:2005.14566v5, citing Feller [22]):
probability measures on the non-negative orthant converge in distribution as soon as their
transforms converge at every `t ≥ 0` to the transform of a probability measure on the orthant.

**Formalization Note.** The statement is for an arbitrary filter, so that `λ ↑ λ*` is covered. The
measures need only be probability measures on the orthant eventually along the filter, because
stationarity is assumed on `(0, λ*)` only. -/
theorem feller_convergence {ι : Type} {n : ℕ} (l : Filter ι) (μ : ι → Measure (Fin n → ℝ))
    (ν : Measure (Fin n → ℝ)) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : ∀ᵐ x ∂ν, ∀ i, 0 ≤ x i)
    (hμ : ∀ᶠ a in l, MeasureTheory.IsProbabilityMeasure (μ a) ∧ ∀ᵐ x ∂(μ a), ∀ i, 0 ≤ x i)
    (hL : ∀ t : Fin n → ℝ, (∀ i, 0 ≤ t i) →
      Tendsto (fun a => laplace (μ a) t) l (𝓝 (laplace ν t))) :
    ConvergesInLaw μ l ν := by sorry

end RedundancyHT
