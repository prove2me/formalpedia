-- Prove2me | Theorems.Thm_RainbowEFX_Sublinear_observation_7
-- name    : RainbowEFX.Sublinear.observation_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:10.852668+00:00
-- url     : https://prove2.me/theorems/38d5f56f-0cfb-4a7e-9940-7adfb31090e4
-- title:
--   Observation 7, p. 10 — a heavily envied set has a most-envious-agent-witness pair; if S is strongly envied, every most envious agent of S strongly envies S
-- statement:
--   Throughout, $[n]$ is the set of agents and $M$ the set of $m$ indivisible goods; agent $i$ has an additive valuation $v_i$ with $v_i(S)=\sum_{g\in S}v_i(\{g\})\ge 0$. A (partial) allocation $X=\langle X_1,\dots,X_n\rangle$ consists of pairwise disjoint bundles, and $P = M\setminus\bigcup_i X_i$ is the set (pool) of unallocated goods.
--
--   Let $0<\varepsilon<1$, let $X$ be an allocation and $S\subseteq M$.
--
--   1. If some agent heavily envies $S$ (that is, $v_i(X_i)<(1-\varepsilon)v_i(S)$), then $S$ has a most-envious-agent-witness pair $(t,Z)$: $Z\subseteq S$, $t$ heavily envies $Z$, and no agent strongly envies $Z$.
--   2. If some agent strongly envies $S$ (heavily envies a proper subset of $S$), then every most envious agent $t$ of $S$ strongly envies $S$.
--
--   The pair $(t,Z)$ is the "champion" and "witness" the update rules U2 and U3 use.
--
--   **Formalization Note** The $\mathcal O(n\cdot|S|^2)$ running time is not formalized. The page states part 2 for the agent $t$ returned by its procedure; it is stated here for every most envious agent of $S$, which includes that output.
-- source:
--   Chaudhury, Garg, Mehlhorn, Mehta, Misra, Improving EFX Guarantees through Rainbow Cycle Number, arXiv:2103.01628v1, p. 10, Observation 7

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

namespace RainbowEFX.Sublinear

open LittleCharity.EFX

theorem observation_7 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (S : Finset (Fin m)) :
    ((∃ i, HeavilyEnvies ε v X i S) → ∃ t Z, IsMEAWitnessPair ε v X S t Z) ∧
    ((∃ i, StronglyEnvies ε v X i S) →
      ∀ t, IsMostEnviousAgent ε v X S t → StronglyEnvies ε v X t S) := by sorry

end RainbowEFX.Sublinear
