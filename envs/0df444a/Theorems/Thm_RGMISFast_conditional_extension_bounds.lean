-- Prove2me | Theorems.Thm_RGMISFast_conditional_extension_bounds
-- name    : RGMISFast.conditional_extension_bounds
-- status  : Proved
-- author  : @srikkanthr
-- created : 2026-11-15T23:38:53.96958+00:00
-- url     : https://prove2.me/theorems/42ccc8f4-784e-459f-9511-78d6285dfee5
-- title:
--   Conditional attached-extension growth and binomial-moment bounds
-- statement:
--   Under the prescribed-rank conditional law of Lemma 5.3, let $0\le\theta<a<b\le\infty$, with a nonempty connected set $A$ active at $\theta$ and prescribed ranks at least $a$. Put $q=e(1-e^{-(b-a)})/(a-\theta)$, interpreting the numerator's parenthesis as $1$ for $b=\infty$. For each integer $k\ge1$,
--   $$\Pr[|\Gamma_{a,b}(A)|\ge k]\le q^k,\qquad \mathbb E\binom{K_{a,b}(A)}k\le q^k.$$
--   The binomial-count random variable is measurable. These are precisely Equations (24) and (25), separated from their subsequent analytic tail consequences. Their common probabilistic input is the expected number of attached active $k$-extensions with ranks below $b$, obtained by conditional exponential thinning and Lemma 5.3.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, §6.1, Lemma 6.1 proof: Equations (24)–(25), printed p.23, and tail bounds paragraph proving Equation (27), printed p.24 (PDF pp.25–26).

import Mathlib
import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open RGMISFast

theorem RGMISFast.conditional_extension_bounds {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (bb : WithTop ℝ)
    (hab : ((a : ℝ) : WithTop ℝ) < bb) :
    (∀ k : ℕ, 1 ≤ k →
      condLaw r₀ θ A rA {r | k ≤ (GammaAB G r a bb A).card} ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      Measurable (fun r : V → ℝ => (KAB G r a bb A).choose k) ∧
      ∫⁻ r, ((KAB G r a bb A).choose k : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) := by sorry
