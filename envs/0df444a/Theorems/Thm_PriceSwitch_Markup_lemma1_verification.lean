-- Prove2me | Theorems.Thm_PriceSwitch_Markup_lemma1_verification
-- name    : PriceSwitch.Markup.lemma1_verification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:56.847742+00:00
-- url     : https://prove2.me/theorems/1b72bcc7-76e8-4973-bd11-37b6edadc7d7
-- title:
--   Lemma 1 — verification of the optimal stopping value
-- statement:
--   Let $N$ be a Poisson counting process of positive rate $\lambda$ under a probability measure $P$. An item sells for $a$ before an admissible stopping time, and the remaining stock then earns terminal revenue $g(m,u)$. Suppose $V(n,t)$ starts from the terminal value, dominates it, and has zero value at zero stock. In its continuation region $V>g$, its time derivative equals the revenue rate less the expected loss from a sale; on the stopping boundary $V=g$, the corresponding derivative inequality holds:
--
--   $$
--   \partial_tV(n,t)=a\lambda-\lambda[V(n,t)-V(n-1,t)]\quad(V>g),\qquad
--   \partial_tV(n,t)\ge a\lambda-\lambda[V(n,t)-V(n-1,t)]\quad(V=g).
--   $$
--
--   Then $V(n,t)$ equals the supremum of expected revenue over admissible switching times. This is the verification result used for the threshold policy.
--
--   **Formalization Note** The printed lemma omits conditions its proof uses: $V(n,0)=g(n,0)$, $V(0,t)=g(0,t)=0$, and $V\ge g$. Local Lipschitz regularity replaces continuity and almost-everywhere differentiability so the integral decomposition is valid. The terminal function is continuous on nonnegative times. The derivative clauses apply at every positive time where a derivative exists. `IsProbabilityMeasure P` is written explicitly although the exponential interarrival law entails it.
-- source:
--   Feng & Gallego (1995), Management Science 41(8), Lemma 1, p. 1378 and proof pp. 1378–1379, https://doi.org/10.1287/mnsc.41.8.1371

import Mathlib
import Definitions.Def_PriceSwitch_Markdown_Model

namespace PriceSwitch.Markup

open MeasureTheory QueueingFundamentals.Foundations

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Feng–Gallego (1995), Lemma 1, p. 1378, with the boundary, obstacle and regularity
conditions required by its proof. -/
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
    ∀ n t, 0 ≤ t → V n t = PriceSwitch.Markdown.stopValue P T a g n t := by sorry

end PriceSwitch.Markup
