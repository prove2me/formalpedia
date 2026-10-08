-- Prove2me | Theorems.Thm_SSPAnalysis_Bellman_lemma2
-- name    : SSPAnalysis.Bellman.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:10:45.976254+00:00
-- url     : https://prove2.me/theorems/1cc20d3c-41e1-4011-8fc4-a80c693e770a
-- title:
--   Lemma 2 — continuity of the Bellman mapping on X
-- statement:
--   Under Assumption 1, the Bellman mapping $T$ of equation (6) is continuous on the destination-zero subspace $X$:
--
--   $$T|_X:X\longrightarrow\mathbb R^n\quad\text{is continuous}.$$
--
--   This supplies the limit passage in the proof of the main fixed-point theorem.
--
--   **Formalization Note.** The paper declares $T:\mathbb R^n\to\mathbb R^n$ even though a real infimum of an unbounded-below family has a default value in Lean. `TRealValued` states explicitly that each control family is nonempty and each Bellman-value family is bounded below. The paper's state $1$ is index `0`, and the rows of $P$ are probability vectors.
-- source:
--   Bertsekas and Tsitsiklis, An Analysis of Stochastic Shortest Path Problems, Math. Oper. Res. 16(3) (1991), p. 586, Lemma 2

import Mathlib
import Definitions.Def_SSPAnalysis_Bellman_SSP

namespace SSPAnalysis.Bellman

open Topology

/-- Lemma 2 (p. 586): continuity of the Bellman mapping on X. -/
theorem lemma2 {n : ℕ} [NeZero n] {U : Fin n → Type*}
    (m : Model n U) (h1 : m.Assumption1)
    (hT : m.TRealValued) :
    ContinuousOn m.T (X n) := by sorry

end SSPAnalysis.Bellman
