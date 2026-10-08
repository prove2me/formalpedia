-- Prove2me | Theorems.Thm_PriceSwitch_Markdown_lemma1_verification
-- name    : PriceSwitch.Markdown.lemma1_verification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:08:14.52917+00:00
-- url     : https://prove2.me/theorems/94708353-05f4-46ff-b913-fdb5732f6b1e
-- title:
--   Lemma 1 — verification of the optimal stopping value
-- statement:
--   Let $N$ be a Poisson counting process with positive rate $\lambda_a$ on a probability space, and let $a$ be its initial price. Let $g(n,t)$ be the revenue available after stopping, with $g(0,t)=0$ and continuous time dependence. Suppose $V(0,t)=0$, $V(n,0)=g(n,0)$, $V(n,t)\ge g(n,t)$, and each $V(n,\cdot)$ is locally Lipschitz for $n\ge1$. At every positive time where its derivative exists, suppose
--
--   $$
--   \frac{\partial V(n,t)}{\partial t}=a\lambda_a-\lambda_a[V(n,t)-V(n-1,t)]\quad\text{if }V(n,t)>g(n,t),
--   $$
--
--   and the left-hand derivative is at least the right-hand expression when $V(n,t)=g(n,t)$. Then $V(n,t)$ equals the optimal expected revenue over stopping times adapted to the history of $N$, bounded by $t$, and stopped before inventory is exhausted.
--
--   This criterion identifies a candidate value function from its differential and boundary properties.
--
--   **Formalization Note** The paper's printed lemma omits conditions used in its proof. The statement explicitly requires the initial-time boundary, the zero-stock boundary for $V$ and $g$, and domination $V\ge g$; local Lipschitz regularity replaces continuity plus almost-everywhere differentiability so that the required integral identity is valid. Continuity of $g$ is retained; its differentiability is not used. A probability-measure instance is recorded explicitly, although the exponential-interarrival law already implies it. The stopping payoff is bounded and measurable; the Poisson counting process is the referenced arrival-process definition.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Lemma 1 and proof, pp. 1378–1379, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markdown

open MeasureTheory QueueingFundamentals.Foundations

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Feng–Gallego (1995), Lemma 1, p. 1378, with the boundary, zero-stock, obstacle and
absolute-continuity conditions used by its proof made explicit. -/
theorem lemma1_verification
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ → Ω → ℝ) (a la : ℝ) (hla : 0 < la)
    (hT : IsExpInterarrivals P la T)
    (g : ℕ → ℝ → ℝ) (hg0 : ∀ u, 0 ≤ u → g 0 u = 0) (hgc : ∀ m, ContinuousOn (g m) (Set.Ici 0))
    (V : ℕ → ℝ → ℝ)
    (hV0 : ∀ u, 0 ≤ u → V 0 u = 0)
    (hVinit : ∀ n, 1 ≤ n → V n 0 = g n 0)
    (hVge : ∀ n, 1 ≤ n → ∀ u, 0 ≤ u → g n u ≤ V n u)
    (hVlip : ∀ n, 1 ≤ n → ∀ R : ℝ, ∃ K, LipschitzOnWith K (V n) (Set.Icc 0 R))
    (h3 : ∀ n, 1 ≤ n → ∀ u, 0 < u → g n u < V n u → ∀ d, HasDerivAt (V n) d u →
      d = a * la - la * (V n u - V (n - 1) u))
    (h4 : ∀ n, 1 ≤ n → ∀ u, 0 < u → V n u = g n u → ∀ d, HasDerivAt (V n) d u →
      a * la - la * (V n u - V (n - 1) u) ≤ d) :
    ∀ n t, 0 ≤ t → V n t = stopValue P T a g n t := by sorry

end PriceSwitch.Markdown
