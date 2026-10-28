-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_observation_11
-- name    : RainbowEFX.Sublinear.observation_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:16.552975+00:00
-- url     : https://prove2.me/theorems/451ee84e-f130-4ee2-9a39-65ba5794bec8
-- title:
--   Observation 11, p. 12 — if agent i heavily envies X_s ∪ g for a source s and an unallocated g, then g is valuable to i
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $0<\varepsilon<1$, let $g$ be an unallocated good and $s$ a source of the envy graph $E_X$. If agent $i$ heavily envies $X_s\cup\{g\}$, then $g$ is valuable to $i$:
--   $$
--   v_i(g)>\varepsilon\cdot v_i(X_i).
--   $$
--
--   This shows that only agents to whom $g$ is valuable can be champions of the sets $X_s\cup\{g\}$, which is why the parts of the group champion graph are small for low-demand goods.
--
--   **Formalization Note** The observation sits in §4, but it holds for every $0<\varepsilon<1$ and is stated so.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 12, Observation 11

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem observation_11 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (g : Fin m) (hg : g ∈ pool X) (s : Fin n)
    (hs : IsSource v X s) (i : Fin n) (hi : HeavilyEnvies ε v X i (insert g (X s))) :
    Valuable ε v X g i := by sorry

end RainbowEFX.Sublinear
