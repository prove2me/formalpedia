-- Prove2me | Theorems.Thm_RankingBeats_General_fact_4_4
-- name    : RankingBeats.General.fact_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:17.493863+00:00
-- url     : https://prove2.me/theorems/c55d830c-7462-4529-a691-40e0ee445612
-- title:
--   Fact 4.4 — a vertex made worse off by removing/inserting v falls to its backup, or to unmatched if it has none
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). Fix distinct vertices $u,v$.
--   1. If $u$ has a backup $b$ with respect to $\vec x$ and becomes worse off by removing $v$ (worse off in $R(\vec x_{-v})$ than in $R(\vec x)$), then $(u,b)\in R(\vec x_{-v})$.
--   2. If $u$ has a backup $b$ with respect to $\vec x_{-v}$ and becomes worse off by inserting $v$ (worse off in $R(\vec x)$ than in $R(\vec x_{-v})$), then $(u,b)\in R(\vec x)$.
--   3. If $u$ has no backup with respect to $\vec x$ and becomes worse off by removing $v$, then $u$ is unmatched in $R(\vec x_{-v})$.
--   4. If $u$ has no backup with respect to $\vec x_{-v}$ and becomes worse off by inserting $v$, then $u$ is unmatched in $R(\vec x)$.
--
--   The worse match is always the backup.
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - reading: backups are defined for matched vertices; 'u_k has no backup' and 'u has no backup' → ¬ HasBackup: no m, b with (u, m) ∈ R(x_{-S}) and (u, b) ∈ R(x_{-(S ∪ {m})}); an unmatched or removed vertex has no backup; reason: Definition 3.5 says 'when no such vertex b exists, u does not have a backup'; for k = 0 in Fact 4.3 the endpoint u_0 = v is removed in x_{-v}, and only this reading gives the clause a meaning
--   - reading: 'If u has no backup ..., then it becomes unmatched in the worse-off matching', with 'respectively' → clauses 3 and 4: conditional on u becoming worse off, once for removing and once for inserting v; reason: 'the worse-off matching' exists only when u becomes worse off, as in the first sentence; both 'respectively' versions are stated
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 14, Fact 4.4

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 4.4** (Worse Match is always the Backup, p. 14). For distinct `u, v`: if `u` has a
backup `b` with respect to `x` (resp. `x_{-v}`) and becomes worse off by removing (resp. inserting)
`v`, then `u` is matched to `b` in `R(x_{-v})` (resp. `R(x)`); if `u` has no backup with respect to
`x` (resp. `x_{-v}`) and becomes worse off, it is unmatched in the worse-off matching. -/
theorem fact_4_4 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (u v : V) (huv : u ≠ v) :
    (∀ b, IsBackup G ∅ x u b →
      BetterOff (ranking G ∅ x) x (ranking G {v} x) x u → s(u, b) ∈ ranking G {v} x) ∧
    (∀ b, IsBackup G {v} x u b →
      BetterOff (ranking G {v} x) x (ranking G ∅ x) x u → s(u, b) ∈ ranking G ∅ x) ∧
    (¬ HasBackup G ∅ x u →
      BetterOff (ranking G ∅ x) x (ranking G {v} x) x u → ¬ IsMatched (ranking G {v} x) u) ∧
    (¬ HasBackup G {v} x u →
      BetterOff (ranking G {v} x) x (ranking G ∅ x) x u → ¬ IsMatched (ranking G ∅ x) u) := by sorry

end RankingBeats.General
