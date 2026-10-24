-- Prove2me | Theorems.Thm_PigeonholeDesign_MultiDim_component_1
-- name    : PigeonholeDesign.MultiDim.component_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:37:19.466547+00:00
-- url     : https://prove2.me/theorems/2066e907-ccff-41e9-8391-64969f8ea2ed
-- title:
--   Proof of Theorem 9, Component 1, p. ec22 — the matched subjects contribute at most ½ c^{1/p} √p T^{1−φ}
-- statement:
--   Fix $p\ge2$ continuous and $q$ discrete covariates, finite supports $S_1,\dots,S_q$, $\varphi\in(0,1)$ and $c>1$, and run the pigeonhole design of Theorem 9 with $m=\lceil c^{-1/p}T^{\varphi}\rceil$ cells per continuous axis on an admissible sequence $x$ of even length $T\ge1$. For **every** outcome of the coins, the matched subjects $\mathcal T_M$ (the subjects among the first $\tau$ paired inside their pigeonhole) satisfy
--   $$d_{A\cap\mathcal T_M,\;B\cap\mathcal T_M}\ \le\ \frac12\,c^{1/p}\sqrt p\;T^{1-\varphi}.$$
--
--   The two subjects of a pair lie in the same pigeonhole, whose diameter is at most $c^{1/p}\sqrt p\,T^{-\varphi}$, and there are at most $\tau/2\le T/2$ pairs. This is Component 1 of the proof of Theorem 9, the $O(T^{1-\varphi})$ term of the bound.
--
--   **Formalization Note** The pigeonholes key subjects by their exact discrete values, so paired subjects have equal discrete coordinates and only the $p$ continuous coordinates contribute to their distance; the printed argument is for $q=0$ and applies verbatim for $q\ge0$. The cell edge is $1/m\le c^{1/p}T^{-\varphi}$, so the printed constant is kept. The matched set is balanced, so the discrepancy on it is a genuine perfect matching.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, p. ec22, proof of Theorem 9, Component 1

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting
import Definitions.Def_PigeonholeDesign_MultiDim_Stopping

namespace PigeonholeDesign.MultiDim

theorem component_1 (p q : ℕ) (hp : 2 ≤ p) (S : Fin q → Finset ℝ) (φ c : ℝ) (hφ0 : 0 < φ)
    (hφ1 : φ < 1) (hc : 1 < c) (T : ℕ) (hT : 1 ≤ T) (hTe : Even T) (x : Fin T → Cov q p)
    (hx : Admissible S x) (coin : Fin T → Bool) :
    PigeonholeDesign.Upper.discrepancyOn x (PigeonholeDesign.Lower.assign (gridHole (cellsPerAxis p c φ T)) x coin)
        (matched (fun t => gridHole (cellsPerAxis p c φ T) (x t))
          (PigeonholeDesign.Lower.assign (gridHole (cellsPerAxis p c φ T)) x coin))
      ≤ (1 / 2) * c ^ ((1 : ℝ) / p) * Real.sqrt p * (T : ℝ) ^ ((1 : ℝ) - φ) := by sorry

end PigeonholeDesign.MultiDim
