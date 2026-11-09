-- Prove2me | Theorems.Thm_TestingEstimation_Dense_penalized_minimum
-- name    : TestingEstimation.Dense.penalized_minimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:12:35.924784+00:00
-- url     : https://prove2.me/theorems/448f1695-cab2-41dd-bad0-f57a2d1884d0
-- title:
--   Lemma 1 — weighted equality and both distance bounds
-- statement:
--   Fix $2\le s\le n$, a graph property $P$, $0<\tau\le1/3$, and a symmetric rational canonical rule $f$ satisfying both guarantees (N2) at the original order $n$. For an ordinary graph $G$, let $E_G(W)=\operatorname{cost}_G(W)+2\operatorname{rej}(W)$ and $M(G)=\min_W E_G(W)$. Then
--
--   $$M(G)=\min_{J\in\mathcal G_V}\{d(G,J)+2\operatorname{rej}(J)\}.$$
--
--   Both sides are attained. Moreover, if $P_n\ne\varnothing$, then
--
--   $$\operatorname{dist}(G,P)-\tau\le M(G)\le\operatorname{dist}(G,P)+2\tau.$$
--
--   Only the distance bounds require the property to be nonempty at this order. The unconditional equality retains empty properties. This is the penalized optimization target for the distance estimator.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: minimum or maximum → real infimum or supremum together with an explicit IsLeast or IsGreatest conclusion; reason: the conclusion includes attainment and excludes a replacement by a merely unattained extremal value
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Lemma 1, p. 10 (PDF 10)

import Definitions.Def_TestingEstimation_Dense_Objective

noncomputable section

namespace TestingEstimation.Dense

theorem penalized_minimum {s n : ℕ} (hs : 2 ≤ s) (hn : s ≤ n)
    (P : Property) (τ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ (1:ℝ)/3)
    (f : Rule s) (hf : SymmetricRule f) (hN2 : CanonicalGuarantees P τ n f)
    (G : Graph n) :
    minimumEnergy f G = graphMinimumEnergy f G ∧
    IsLeast (Set.range (energy f G)) (minimumEnergy f G) ∧
    IsLeast (Set.range (fun J : Graph n => editDistance G J + 2 * graphRej f J))
      (graphMinimumEnergy f G) ∧
    ((P.graphs n).Nonempty →
      distance P G - τ ≤ minimumEnergy f G ∧
      minimumEnergy f G ≤ distance P G + 2*τ) := by sorry

end TestingEstimation.Dense
