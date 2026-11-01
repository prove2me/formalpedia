-- Prove2me | Theorems.Thm_SerialBatchTardy_early_processing_le
-- name    : SerialBatchTardy.early_processing_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:52.756196+00:00
-- url     : https://prove2.me/theorems/1a073d56-4d9a-4f03-a42f-41a3e8b48b19
-- title:
--   Lemma 11, proof — early jobs have total processing at most $kt$ (corrected: $x_i < t$)
-- statement:
--   Let $x_1,\dots,x_n$ be distinct positive integers, each smaller than $t$, with $(k-1)x_i<t$ for all $i$. In every feasible schedule of the constructed instance with $\sum_jw_jU_j$ at most the bound $S\,(kX-t+(n-1)k)$, the early jobs have total processing time at most $kt$, for every leftover list $L$.
--
--   This is the counting step of the converse direction.
--
--   Differences from the source:
--   - reading: "∑_{ℓ=1}^{2k} p(B_ℓ) ≤ kt" for the batches B_1, …, B_{2k} of Lemma 10 → the early jobs of any feasible schedule within the bound have total processing time ≤ kt; reason: in the form of Lemma 10 the batches B_1, …, B_{2k} hold exactly the early jobs; Lemma 10 itself moves unit leftover jobs and is not stated, so the step is stated for every schedule
--   - correction: standing assumption "k − 1 times the largest integer in {x_1, …, x_n} is less than t" (p.550) → every x_i < t; reason: at k = 1 the printed assumption only says 0 < t and this step is false: k = 1, t = 2, xs = (5, 6); the schedule with all of J_5 in one batch [0, 7) is within the bound and its early jobs have processing 5 > kt = 2; for k ≥ 2 the printed assumption implies x_i < t, so every k ≥ 2 instance of the source is covered (the proof itself uses "all x_i are smaller than t", p.551)
--   - generalization: (k − 1)t leftover jobs of processing time 1 → an arbitrary list L of leftover processing times (each leftover job keeps weight S·k(X+n), release 0, due date 3kt); reason: L = List.replicate ((k−1)t) 1 satisfies every hypothesis placed on L, so the printed lemma is the special case
--   - encoding: weights n^h + n^h/x_i and k(X + n), bound kX − t + (n − 1)k → all multiplied by S = ∏ x_i (weights n^h·(S + S/x_i) and S·k(X + n); bound S·(k(X + n) − (t + k)) in ℤ); reason: p.551 makes the weights integral exactly this way ("multiplying them with ∏ x_i"); the comparison is in ℤ so that no truncated subtraction occurs
--   - reading: "S_{B′} ∉ [S_B, C_B) for any batch B′ ≠ B" (p.546), "no two batches are processed at the same time" (p.548) → for distinct used batches, C_B ≤ S_{B′} or C_{B′} ≤ S_B; reason: the two agree for batches of positive length; they differ only when a batch of length 0 (Δ = 0, all its p_j = 0) starts together with another batch, where the literal p.546 condition breaks the time reversal of Lemma 12 (Δ = 0, jobs (p, r, d) = (0, 0, 0) and (1, 0, 1): cost > 0, reversed cost 0)
--   - encoding: start times S_B (domain not stated) → start times in ℤ; reason: all data are integers; rounding every start time down keeps a schedule feasible and keeps every early job early
--   - generalization: x_i ∈ {1, …, n^{ck}} written in base n (p.550) → no range bound on the x_i and no condition on n; reason: the argument uses only the totals of each J_{x,ℓ}, which hold for the base-n digits of any x in any base (Nat.ofDigits_digits), so the instances of the source are included
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), Lemma 11, proof, p.553 (PDF p.9), "we have ∑_{ℓ=1}^{2k} p(B_ℓ) ≤ kt"

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **The early jobs have total processing time at most `kt`** (Hermelin, Mnich & Omlor,
J. Scheduling 27 (2024), proof of Lemma 11, p.553, PDF p.9: "Since there are 2k batches with early
jobs, and the setup time for each of these batches is t, we have ∑_{ℓ=1}^{2k} p(B_ℓ) ≤ kt").
Let `xs` be a duplicate-free list of positive integers, each smaller than `t`, with
`(k − 1)·x_i < t`. In every feasible schedule of the constructed instance whose weighted number of
tardy jobs is at most the bound, the early jobs have total processing time at most `kt`, whatever
the leftover list `L`.

**Formalization Note.** Weights and bound are scaled by `S = ∏ x_i`. -/
theorem early_processing_le (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup)
    (hpos : ∀ a ∈ xs, 1 ≤ a) (hstand : ∀ a ∈ xs, ((k : ℤ) - 1) * a < t) (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k) :
    ∑ j ∈ Finset.univ.filter (fun j => ¬ σ.IsTardy j), ((hardInstance xs t k L).job j).p ≤
      k * t := by sorry

end SerialBatchTardy
