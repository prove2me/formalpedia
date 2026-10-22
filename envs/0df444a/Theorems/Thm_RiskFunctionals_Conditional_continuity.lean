-- Prove2me | Theorems.Thm_RiskFunctionals_Conditional_continuity
-- name    : RiskFunctionals.Conditional.continuity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:41.683401+00:00
-- url     : https://prove2.me/theorems/e1a0a2f2-9cec-4f8b-be9a-e0ea81e20c29
-- title:
--   Theorem 2.54 — a locally lower bounded conditional acceptability mapping is continuous
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $\mathcal F_1\subseteq\mathcal F$ a sub-$\sigma$-field and $1\le p<\infty$. Let $\mathcal K$ be the cone of $\mathbb P$-a.s. non-negative random variables in $L_p(\mathcal F_1)$, and let $\mathcal A:L_p(\mathcal F)\to L_p(\mathcal F_1)$ be a conditional acceptability mapping. Suppose $\mathcal A$ is lower bounded on a neighborhood of some $Y_0\in L_p(\mathcal F)$: there are a neighborhood $\mathcal U$ of zero in $L_p(\mathcal F)$ and a bounded subset $B$ of $L_p(\mathcal F_1)$ with
--   $$\mathcal A(Y)\in B+\mathcal K\qquad\text{for all }Y\in Y_0+\mathcal U.$$
--   Then $\mathcal A$ is continuous on $L_p(\mathcal F)$.
--
--   This is the conditional counterpart of the automatic continuity of concave functionals bounded below near a point, and it gives continuity of the conditional mappings of Examples 2.53.
--
--   **Formalization Note** $\mathcal A(Y)\in B+\mathcal K$ is written as: some $b\in B$ satisfies $b\le\mathcal A(Y)$ almost surely. $B$ is a subset of `Lp ℝ p P` contained in `lpMeas ℝ ℝ m p P` and bounded in the $L_p$ norm; $\mathcal U$ is a neighborhood of $0$ (so $Y_0+\mathcal U$ is a neighborhood of $Y_0$, the book's reading). Continuity is in the $L_p$ norm topologies, for the map with values in `Lp ℝ p P`, whose subspace topology on $L_p(\mathcal F_1)$ is the norm topology.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 73, Theorem 2.54

import Mathlib
import Definitions.Def_RiskFunctionals_Conditional_Mappings

namespace RiskFunctionals.Conditional

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 73,
Theorem 2.54: let `𝒜 : L_p(ℱ) → L_p(ℱ₁)` be a conditional acceptability mapping, `1 ≤ p < ∞`.
If `𝒜` is lower bounded on a neighborhood of some `Y₀`, i.e. there are a neighborhood `𝒰` of
zero and a bounded set `B ⊆ L_p(ℱ₁)` with `𝒜(Y) ∈ B + K` for all `Y ∈ Y₀ + 𝒰` (`K` the cone of
a.s. non-negative elements of `L_p(ℱ₁)`, so `𝒜(Y) ∈ B + K` means `b ≤ 𝒜(Y)` a.s. for some
`b ∈ B`), then `𝒜` is continuous on `L_p(ℱ)`. -/
theorem continuity {Ω : Type*} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (P : Measure[mΩ] Ω) [IsProbabilityMeasure P]
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (A : Lp ℝ p P → lpMeas ℝ ℝ m p P) (hA : IsConditionalAcceptabilityMapping A)
    (Y₀ : Lp ℝ p P) (U : Set (Lp ℝ p P)) (hU : U ∈ nhds (0 : Lp ℝ p P))
    (Bset : Set (Lp ℝ p P)) (hB_sub : Bset ⊆ lpMeas ℝ ℝ m p P)
    (hB_bdd : Bornology.IsBounded Bset)
    (hlow : ∀ Y ∈ U, ∃ b ∈ Bset, ∀ᵐ ω ∂P, b ω ≤ (A (Y₀ + Y) : Lp ℝ p P) ω) :
    Continuous (fun Y : Lp ℝ p P => (A Y : Lp ℝ p P)) := by sorry

end RiskFunctionals.Conditional
