-- Prove2me | Theorems.Thm_SensitivityRowCounting_shared_labeling_12607
-- name    : SensitivityRowCounting.shared_labeling_12607
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-20T15:30:22.897576+00:00
-- url     : https://prove2.me/theorems/6ac66962-64e7-4939-970b-0672f6c94262
-- title:
--   Simultaneous defect thresholds from exact source-row counting
-- statement:
--   Every loopless tournament on 12607 vertices admits a single binary labeling of its directed edges with the following five simultaneous properties. For q in {0,1,2,3,4}, put T_q=[24,31,38,44,50]_q. For every subset I of vertices and every assignment of a binary target color c_j to each vertex, if every i in I has at most q outgoing arcs i→j within I whose labels differ from c_j, then |I|<T_q. Values of the labeling on non-arcs are unused. The tournament is arbitrary. This is a stronger higher-tolerance labeling certificate for the sensitivity construction; it does not alone assert an exponent improvement.
-- source:
--   Original research note for yousofy with Codex, 20 October 2026, 'A sharper simultaneous tournament-labeling certificate', sections Exact row count through Five exact certificates. Mathematical proof independently audited; not yet kernel-checked. Let F_q(d)=sum_{a≤q} choose(d,a). For fixed I,c of size t, labels on outgoing rows are independent and the exact probability is 2^{-choose(t,2)} product_i F_q(d_i). The degree sum is choose(t,2). Log-concavity of F_q balances this product: B_q(t)=F_q((t−1)/2)^t for odd t, and (F_q(t/2−1)F_q(t/2))^(t/2) for even t. For cutoffs [24,31,38,44,50], the sum of K^t 2^t B_q(t)/(t! 2^choose(t,2)) is less than 833/1000: individual upper bounds are 60/1000,770/1000,1/1000,1/1000,1/1000. Exact product bases for q=1,2,3,4 are 16,32852,2802228,197839476. A union bound leaves a labeling avoiding all five bad-set sizes. Larger sets restrict to a forbidden cutoff-sized set. The local Python exact-integer certificate and full prose proof are in the accompanying research package. Retains the tournament-labeling provenance of Robin Kothari/Codex, accepted foundation https://prove2.me/theorems/49fdd176-c319-4f1e-b15f-b1fd5130f0bc, and OpenAI's sensitivity construction.

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
open scoped Classical

namespace SensitivityRowCounting
theorem shared_labeling_12607
    (A : Fin 12607 → Fin 12607 → Prop)
    (hloop : ∀ i, ¬ A i i)
    (hcomp : ∀ {i j}, i ≠ j → (A i j ↔ ¬ A j i)) :
    ∃ label : Fin 12607 → Fin 12607 → Fin 2,
      ∀ q : Fin 5, ∀ I : Finset (Fin 12607),
      ∀ colors : Fin 12607 → Fin 2,
        (∀ i ∈ I, (I.filter (fun j => A i j ∧ label i j ≠ colors j)).card ≤ q.val) →
        I.card < (![24,31,38,44,50] q) := by sorry
end SensitivityRowCounting
