-- Prove2me | Theorems.Thm_PigeonholeDesign_MultiDim_unmatched_imbalance
-- name    : PigeonholeDesign.MultiDim.unmatched_imbalance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:37:23.894391+00:00
-- url     : https://prove2.me/theorems/480ab5a7-398f-43b4-ac32-9cc60ce09bda
-- title:
--   Proof of Theorem 9, p. ec22 — at most one unmatched subject per pigeonhole, H ≤ (number of pigeonholes), |H⁰_τ − H¹_τ| = T − τ
-- statement:
--   In the setting of Theorem 9 (with $m=\lceil c^{-1/p}T^{\varphi}\rceil$ cells per continuous axis, $T\ge1$ even and $x$ admissible), for every outcome of the coins:
--
--   1. no two unmatched subjects among the first $\tau$ share a pigeonhole;
--   2. $H=H^0_\tau+H^1_\tau$ is at most the number of pigeonholes that admissible covariates can occupy,
--   $$H^0_\tau+H^1_\tau\ \le\ \Big(\prod_{i=1}^q m_i\Big)\,m^p ,\qquad m_i=|S_i| ;$$
--   3. the imbalance of the unmatched subjects equals the number of subjects arriving after $\tau$,
--   $$\big|H^0_\tau-H^1_\tau\big|=T-\tau .$$
--
--   Item 3 holds because the matched pairs are balanced and at time $\tau$ one group has $T/2$ subjects and the other $\tau-T/2$. Component 2 of the proof starts from these facts.
--
--   **Formalization Note** The printed bound $H\le\frac1cT^{p\varphi}$ is the count of continuous cells for $q=0$ before rounding. With the ceiling $m$ the count is $m^p$, and the discrete supports multiply it by $\prod_i m_i$. Both changes follow from the pigeonholes actually used.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec22, proof of Theorem 9, Component 2 (first two paragraphs)

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_MultiDim_Stopping

namespace PigeonholeDesign.MultiDim

theorem unmatched_imbalance (p q : ℕ) (hp : 2 ≤ p) (S : Fin q → Finset ℝ) (φ c : ℝ)
    (hφ0 : 0 < φ) (hφ1 : φ < 1) (hc : 1 < c) (T : ℕ) (hT : 1 ≤ T) (hTe : Even T)
    (x : Fin T → Cov q p) (hx : Admissible S x) (coin : Fin T → Bool) :
    let m := cellsPerAxis p c φ T
    let cell := fun t => gridHole m (x t)
    let w := PigeonholeDesign.Lower.assign (gridHole m) x coin
    (∀ s ∈ unmatched cell w, ∀ s' ∈ unmatched cell w, cell s = cell s' → s = s') ∧
      H0 cell w + H1 cell w ≤ (∏ i, (S i).card) * m ^ p ∧
      |(H0 cell w : ℤ) - H1 cell w| = (T : ℤ) - tau w := by sorry

end PigeonholeDesign.MultiDim
