-- Prove2me | Theorems.Thm_RideHailingAV_PureHV_lemma_1_min_supply_inverse
-- name    : RideHailingAV.PureHV.lemma_1_min_supply_inverse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:08.363686+00:00
-- url     : https://prove2.me/theorems/ce7c6c3d-b5fb-41a4-90fa-70447cbc1e10
-- title:
--   Lemma 1, Item 2 — $\underline n$ is strictly increasing and invertible
-- statement:
--   Let $t_1(s)=as^{-r}$ with $a>0$, $0\le r<1$, and trip time $t_2>0$. The minimal supply $\underline n$ is strictly increasing on $[0,\infty)$ and maps $[0,\infty)$ bijectively onto $[0,\infty)$. Hence it has an inverse $\bar d(n)$, defined for every fleet size $n\ge0$; $\bar d(n)$ is the highest demand rate that a fleet of $n$ vehicles can supply.
--
--   Strict monotonicity of $\underline n$ is used again in the proof of Proposition 1, Item 4.
--
--   Differences from the source:
--   - reading: n(d) has an inverse function d̄(n) → n is strictly increasing on [0, ∞) and a bijection of [0, ∞) onto [0, ∞); reason: the proof (p. 39) derives the inverse from strict monotonicity; surjectivity onto [0, ∞) makes d̄ defined at every fleet size; together they give the inverse and its monotonicity
--   - encoding: the model constants a, t₂ (and V, mᵢ where used) of the ETA function, trip time, value support and demand mass → explicit hypotheses 0 < a, 0 < t₂ (0 < V, 0 < m where used); reason: implicit in the model: ã > 0 is stated on p. 12 and ã > 0 iff a > 0; t₂ is a trip time; V is the top of the value support [0, V]; (3) divides by mᵢ
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Lemma 1, Item 2, p. 38 (proof p. 39)

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_minSupply

namespace RideHailingAV.PureHV

/-- **Lemma 1, Item 2 — `n(d)` is strictly increasing and has an inverse.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Lemma 1,
Item 2, p. 38, with its proof on p. 39: "`n(d)` is strictly increasing in `d`. Thus, by the inverse
function theorem, its inverse function `d̄(n)` exists and is strictly increasing in `n`."

For `a > 0`, `0 ≤ r < 1`, `t₂ > 0`: `n` is strictly increasing on `[0, ∞)` and maps `[0, ∞)`
bijectively onto `[0, ∞)`, so its inverse `d̄` is defined on every fleet size `n ≥ 0`. -/
theorem lemma_1_min_supply_inverse (M : Market) (ha : 0 < M.a) (hr0 : 0 ≤ M.r)
    (hr1 : M.r < 1) (ht2 : 0 < M.t2) :
    StrictMonoOn (minSupply M) (Set.Ici 0) ∧
      Set.BijOn (minSupply M) (Set.Ici 0) (Set.Ici 0) := by sorry

end RideHailingAV.PureHV
