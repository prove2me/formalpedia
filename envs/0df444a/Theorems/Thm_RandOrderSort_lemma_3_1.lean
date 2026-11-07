-- Prove2me | Theorems.Thm_RandOrderSort_lemma_3_1
-- name    : RandOrderSort.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:31.085992+00:00
-- url     : https://prove2.me/theorems/61a3e219-511b-4fad-9d57-a5692c10df71
-- title:
--   Lemma 3.1 — capacities and feasibility of the schedule
-- statement:
--   For $n\ge 16T=8192$, the shrinking schedule satisfies $167\le B\le 338$. Every bucket in a nonfinal shrinking phase has capacity in $[B,B+7]$, and the final phase has
--   $$M_k<515$$
--   available cells. The phases tile the arrivals $T,\dots,n-1$, and the initial block and the fresh blocks tile the $n$ cells; all of these quantities are functions of $n$ alone.
--
--   For every $n\ge 2$ and every execution, the complete algorithm is legal: the run raises no fault, its allocated prefix ends at cell $n$, and the $n$ arrivals occupy the $n$ cells bijectively.
--
--   These bounds supply the capacity thresholds of the probability analysis, and they show that the algorithm completes every input order, whichever buckets overflow.
--
--   **Formalization Note** "No fault" means that every placement and reassignment finds an admissible bucket, every reallocation fills exactly its capacities, and no fresh block passes cell $n$.
--
--   Differences from the source:
--   - encoding: all phase lengths and allocation times are deterministic functions of n → the functions `phaseStart`, `phaseLen`, `phaseFresh` of n, which the run follows by definition, with the tiling identities stated; reason: Lean functions of n; the identities say that the run uses them consistently
--   - encoding: legal on every input order, uses exactly n physical cells, places all n arrivals → no fault flag, allocated prefix of length n, and the cell map a bijection onto 0, …, n−1, for all x, π, σ; reason: every operation's legality is what the fault flag records
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 3.1, p.14

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort

namespace RandOrderSort

/-- **Lemma 3.1 (Capacities and feasibility)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.14: "The shrinking schedule satisfies
167 ≤ B ≤ 338. Every bucket in a nonfinal shrinking phase has capacity in [B, B + 7], and the
final phase has M_k < 515 available cells. The complete algorithm is legal on every input order,
uses exactly n physical cells, and places all n arrivals. All phase lengths and allocation times
are deterministic functions of n."

**Formalization Note.** The schedule clauses are stated for `n ≥ 16T = 8192`, where the schedule is
used. Phase lengths and allocation sizes are the functions `phaseStart`, `phaseLen`, `phaseFresh` of
`n` alone, which the run follows by construction; the lemma states that they tile the arrivals
`T, …, n − 1` and the cells `T, …, n − 1`. Legality is stated for every `n ≥ 2` (the consecutive branch
`n < 8192` included): the run raises no fault (every placement and every reassignment finds an
admissible bucket, every reallocation fills exactly its capacities, no fresh block passes cell
`n`), its allocated prefix ends at `n`, and the output cells form a bijection onto `0, …, n − 1`. -/
theorem lemma_3_1 :
    (∀ n, 16 * T ≤ n →
      167 ≤ B n ∧ B n ≤ 338 ∧
      (∀ i, 1 ≤ i → i < k n → ∀ ℓ < b n i, B n ≤ shrinkCap n i ℓ ∧ shrinkCap n i ℓ ≤ B n + 7) ∧
      M n (k n) < 515 ∧
      phaseStart n 0 = T ∧
      (∀ p, p + 1 < numPhases n → phaseStart n (p + 1) = phaseStart n p + phaseLen n p) ∧
      phaseStart n (numPhases n - 1) + phaseLen n (numPhases n - 1) = n ∧
      T + ∑ p ∈ Finset.range (numPhases n), phaseFresh n p = n) ∧
    ∀ n, 2 ≤ n → ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)),
      (runOf x π σ).fault = false ∧ (runOf x π σ).alloc = n ∧
      Function.Injective (cellOf empiricalSort x π σ) ∧ ∀ t, cellOf empiricalSort x π σ t < n := by sorry

end RandOrderSort
