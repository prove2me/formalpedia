-- Prove2me | Theorems.Thm_PersistClust_Count_stratum_sweep_equality
-- name    : PersistClust.Count.stratum_sweep_equality
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T05:12:28.738085+00:00
-- url     : https://prove2.me/theorems/0d1b3715-4ef4-4197-8799-14307c2891d9
-- title:
--   Stratum sweep equality: the level-u census of classes born at b equals the filtered diagram sum over bars with birth b and death below u
-- statement:
--   Let $M$ be a tame one-parameter persistence module: a filtered family of finite components indexed by the real line, governed by a filtration law, with a finite critical set $\mathrm{critSet}$ and a persistence diagram whose bar with birth $p$ and death $q$ carries multiplicity $\mu(p,q)$; the essential bar has death $q = \bot$ (the extended-real bottom). Assume the diagram has finite support: only finitely many points of the extended plane carry positive multiplicity. Fix a real birth value $b$ and a census level $u < b$ that is not a critical value ($u \notin \mathrm{critSet}$). Write $N_u(b)$ for the number of components present at level $u$ whose birth supremum is exactly $b$, and $\Sigma_u(b)$ for the sum of diagram multiplicities over all bars with birth exactly $b$ and death strictly below $u$: $$N_u(b) \;=\; \Sigma_u(b) \;=\; \sum_{d < u} \mu(b, d),$$ where the essential bar $(b, \bot)$ is included (its death lies below every real level) and bars with death exactly $u$ are excluded (no bar dies at the crit-free level $u$). The sweep equality states that the level-$u$ census of the birth-$b$ stratum equals this filtered diagram mass. This is the level-by-level bridge between interleaving census counts and persistence-diagram multiplicities: it converts counting arguments over classes born at a fixed value into counting arguments over diagram bars, and is the engine behind the Hall-type matching arguments used in persistence-based clustering. Formalization note: components, structure maps and birth suprema are the platform's comps/structMap/birthSup structures; $\mu$ is mult of rankFn over the finite diagonal diagram t2_finDiag; deaths below $u$ are read in the extended-real order with $\bot$ minimal.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the birth-stratum census sweep equality (stratum census at a crit-free level equals the filtered diagram sum over deaths below the level), the counting engine of the joint-Hall sector. Transcribed GREEN (exit 0, sorry-free) from the working file; the 41-declaration helper chain (comb census stability, gap windows, rank jumps, alive-up monotonicity, the finite diagonal diagram) inlined verbatim above the target, with the platform t3_comb argument order.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem stratum_sweep_equality {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    (b u : ℝ) (hfin : {p : EReal × EReal | mult (rankFn stage J) p ≠ 0}.Finite) :
    u ∉ (critSet hTame : Set ℝ) → u < b →
    ({C : comps stage J u | birthSup hLaw u C = b} :
      Set (comps stage J u)).encard =
    ∑ p ∈ ((Set.Finite.toFinset hfin).filter
        (fun p => p.1 = ((b : EReal)) ∧ p.2 < ((u : EReal)))),
      mult (rankFn stage J) p
    := by sorry
