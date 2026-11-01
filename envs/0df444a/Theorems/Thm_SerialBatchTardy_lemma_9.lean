-- Prove2me | Theorems.Thm_SerialBatchTardy_lemma_9
-- name    : SerialBatchTardy.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:48.681116+00:00
-- url     : https://prove2.me/theorems/3b04cca8-b262-4d82-998a-400d9927d2ea
-- title:
--   Lemma 9 — every $E_\ell$ is nonempty
-- statement:
--   Let $x_1,\dots,x_n$ be distinct positive integers with $(k-1)x_i<t$ for all $i$. In every feasible schedule of the constructed instance with $\sum_jw_jU_j$ at most the bound $S\,(kX-t+(n-1)k)$, the set $E_\ell$ is nonempty for every $\ell\in\{0,\dots,k-1\}$.
--
--   Differences from the source:
--   - generalization: the schedule of Lemma 6 → every feasible schedule within the bound, any leftover list L; reason: the lemma uses only the bound and feasibility
--   - encoding: weights n^h + n^h/x_i and k(X + n), bound kX − t + (n − 1)k → all multiplied by S = ∏ x_i (weights n^h·(S + S/x_i) and S·k(X + n); bound S·(k(X + n) − (t + k)) in ℤ); reason: p.551 makes the weights integral exactly this way ("multiplying them with ∏ x_i"); the comparison is in ℤ so that no truncated subtraction occurs
--   - encoding: ℓ ∈ {1, …, k}, release date (ℓ − 1)3t → ℓ ∈ {0, …, k − 1}, release date ℓ·3t; reason: 0-based indices
--   - reading: "S_{B′} ∉ [S_B, C_B) for any batch B′ ≠ B" (p.546), "no two batches are processed at the same time" (p.548) → for distinct used batches, C_B ≤ S_{B′} or C_{B′} ≤ S_B; reason: the two agree for batches of positive length; they differ only when a batch of length 0 (Δ = 0, all its p_j = 0) starts together with another batch, where the literal p.546 condition breaks the time reversal of Lemma 12 (Δ = 0, jobs (p, r, d) = (0, 0, 0) and (1, 0, 1): cost > 0, reversed cost 0)
--   - encoding: start times S_B (domain not stated) → start times in ℤ; reason: all data are integers; rounding every start time down keeps a schedule feasible and keeps every early job early
--   - generalization: x_i ∈ {1, …, n^{ck}} written in base n (p.550) → no range bound on the x_i and no condition on n; reason: the argument uses only the totals of each J_{x,ℓ}, which hold for the base-n digits of any x in any base (Nat.ofDigits_digits), so the instances of the source are included
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), Lemma 9, p.552 (PDF p.8)

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **Lemma 9** (Hermelin, Mnich & Omlor, J. Scheduling 27 (2024), p.552, PDF p.8). Let `xs` be a
duplicate-free list of positive integers with `(k − 1)·x_i < t` for all `i`. In every feasible
schedule of the constructed instance whose weighted number of tardy jobs is at most the bound, the
set `E_ℓ` of early normal jobs of type `ℓ` is nonempty for every `ℓ < k`.

**Formalization Note.** Weights and bound are scaled by `S = ∏ x_i`; `ℓ` is 0-based. -/
theorem lemma_9 (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (hpos : ∀ a ∈ xs, 1 ≤ a)
    (hstand : ∀ a ∈ xs, ((k : ℤ) - 1) * a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k) :
    ∀ ℓ < k, (earlyType σ ℓ).Nonempty := by sorry

end SerialBatchTardy
