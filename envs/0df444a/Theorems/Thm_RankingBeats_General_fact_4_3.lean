-- Prove2me | Theorems.Thm_RankingBeats_General_fact_4_3
-- name    : RankingBeats.General.fact_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:28:33.167286+00:00
-- url     : https://prove2.me/theorems/234e0c77-7da0-444f-96fd-e36cb94088fe
-- title:
--   Fact 4.3 — consecutive vertices of the alternating path are backups
-- statement:
--   $G=(V,E)$ is a finite simple graph and $\vec x$ a rank vector with values in $[0,1)$ and pairwise distinct ranks; $R(\cdot)$ is Ranking (Algorithm 1). Fix a vertex $v$ and let $\mathrm{AltPath}(\vec x,\vec x_{-v})=(u_0,\dots,u_k)$ with $u_0=v$. Then
--   - for each odd $i<k$, $u_{i+1}$ is the backup of $u_i$ with respect to $\vec x$;
--   - for each even $2\le i<k$, $u_{i+1}$ is the backup of $u_i$ with respect to $\vec x_{-v}$;
--   - for odd $k$, $u_k$ has no backup with respect to $\vec x$; for even $k$, $u_k$ has no backup with respect to $\vec x_{-v}$.
--
--   $$u_{i+1}=\mathrm{backup}_{\vec x}(u_i)\ (i\text{ odd}),\qquad u_{i+1}=\mathrm{backup}_{\vec x_{-v}}(u_i)\ (i\text{ even}\ge2).$$
--   It identifies the alternating path as a chain of backups.
--
--   Differences from the source:
--   - encoding: no two vertices have the exact same rank (W.L.O.G., p. 11: ties have probability zero) → hypothesis Function.Injective x; reason: the paper's standing assumption on a fixed rank vector, made an explicit binder
--   - reading: backups are defined for matched vertices; 'u_k has no backup' and 'u has no backup' → ¬ HasBackup: no m, b with (u, m) ∈ R(x_{-S}) and (u, b) ∈ R(x_{-(S ∪ {m})}); an unmatched or removed vertex has no backup; reason: Definition 3.5 says 'when no such vertex b exists, u does not have a backup'; for k = 0 in Fact 4.3 the endpoint u_0 = v is removed in x_{-v}, and only this reading gives the clause a meaning
--   - encoding: AltPath(x, x_{-v}) = (u_0, ..., u_k) → hypothesis IsPathFrom (altPath G x v) v p, with u_i = p.getD i v and k = p.length - 1; reason: the path with u_0 = v of Lemma 4.1
--   - generalization: the standing assumption on p. 11 that the underlying graph admits a perfect matching → no perfect-matching hypothesis on G; reason: these structural statements concern the Ranking run, not OPT; adding the standing perfect-matching assumption specializes each statement to the complete source claim
-- source:
--   Derakhshan, Yu, Ranking Beats 1-1/e on General Graphs, STOC 2027 submission (manuscript sha256 6715d477…), p. 14, Fact 4.3

import Mathlib
import Definitions.Def_RankingBeats_General_Ranking
import Definitions.Def_RankingBeats_General_QueryCommit
import Definitions.Def_RankingBeats_General_Structures

open Classical MeasureTheory

namespace RankingBeats.General

/-- **Fact 4.3** (Backups in Alternating Path, p. 14). Let `AltPath(x, x_{-v}) = (u_0, …, u_k)`.
For odd `i < k`, `u_{i+1}` is the backup of `u_i` with respect to `x`; for even `2 ≤ i < k`,
`u_{i+1}` is the backup of `u_i` with respect to `x_{-v}`; for odd (even) `k`, `u_k` has no backup
with respect to `x` (`x_{-v}`). -/
theorem fact_4_3 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (x : V → ℝ)
    (hx : ∀ z, x z ∈ Set.Ico (0 : ℝ) 1) (hinj : Function.Injective x) (v : V) (p : List V)
    (hp : IsPathFrom (altPath G x v) v p) :
    (∀ i, Odd i → i < p.length - 1 → IsBackup G ∅ x (p.getD i v) (p.getD (i + 1) v)) ∧
    (∀ i, Even i → 2 ≤ i → i < p.length - 1 →
      IsBackup G {v} x (p.getD i v) (p.getD (i + 1) v)) ∧
    (Odd (p.length - 1) → ¬ HasBackup G ∅ x (p.getD (p.length - 1) v)) ∧
    (Even (p.length - 1) → ¬ HasBackup G {v} x (p.getD (p.length - 1) v)) := by sorry

end RankingBeats.General
