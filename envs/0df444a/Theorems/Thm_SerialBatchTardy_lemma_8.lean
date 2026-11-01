-- Prove2me | Theorems.Thm_SerialBatchTardy_lemma_8
-- name    : SerialBatchTardy.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:57.247919+00:00
-- url     : https://prove2.me/theorems/b2717169-3117-429a-9b9d-5688a8e3cd47
-- title:
--   Lemma 8 — $p(E_\ell)\le x_{\pi(\ell)}$ and $w(E_\ell)\le S(p(E_\ell)+1)$ (corrected: $x_i < t$)
-- statement:
--   Let $x_1,\dots,x_n$ be distinct positive integers, each smaller than $t$, and let $\sigma$ be a feasible schedule of the constructed instance. Let $x_{\pi(\ell)}$ be the least input integer among the jobs of $E_\ell$ (so $E_\ell\neq\emptyset$). Then
--
--   1. $p(E_\ell)\le x_{\pi(\ell)}$;
--   2. $w(E_\ell)\le S\,(p(E_\ell)+1)$, with equality if and only if $E_\ell=J_{x_{\pi(\ell)},\ell}$.
--
--   Here $S=\prod_ix_i$. These bounds compare the weight of early jobs with their processing time.
--
--   Differences from the source:
--   - correction: standing assumption "k − 1 times the largest integer in {x_1, …, x_n} is less than t" (p.550) → every x_i < t; reason: at k = 1 the printed assumption only says 0 < t and Lemma 8 is false: k = 1, t = 2, xs = (5, 100), n = 2; J_{5} = jobs of length 1, 4 (due 7), J_{100} = jobs 4, 32, 64 (due 102); batches [0, 7) with the jobs 1, 4 of J_5 and [7, 73) with the job 64 of J_100 make all three early, so p(E_1) = 69 > 5; for k ≥ 2 the printed assumption implies x_i < t, so every k ≥ 2 instance of the source is covered (the proof itself uses "all x_i are smaller than t", p.551)
--   - generalization: the schedule of Lemma 6 (within the bound) → every feasible schedule, any leftover list L; reason: the lemma uses only feasibility
--   - encoding: weights n^h + n^h/x_i and k(X + n), bound kX − t + (n − 1)k → all multiplied by S = ∏ x_i (weights n^h·(S + S/x_i) and S·k(X + n); bound S·(k(X + n) − (t + k)) in ℤ); reason: p.551 makes the weights integral exactly this way ("multiplying them with ∏ x_i"); the comparison is in ℤ so that no truncated subtraction occurs
--   - encoding: ℓ ∈ {1, …, k}, release date (ℓ − 1)3t → ℓ ∈ {0, …, k − 1}, release date ℓ·3t; reason: 0-based indices
--   - reading: "S_{B′} ∉ [S_B, C_B) for any batch B′ ≠ B" (p.546), "no two batches are processed at the same time" (p.548) → for distinct used batches, C_B ≤ S_{B′} or C_{B′} ≤ S_B; reason: the two agree for batches of positive length; they differ only when a batch of length 0 (Δ = 0, all its p_j = 0) starts together with another batch, where the literal p.546 condition breaks the time reversal of Lemma 12 (Δ = 0, jobs (p, r, d) = (0, 0, 0) and (1, 0, 1): cost > 0, reversed cost 0)
--   - encoding: start times S_B (domain not stated) → start times in ℤ; reason: all data are integers; rounding every start time down keeps a schedule feasible and keeps every early job early
--   - generalization: x_i ∈ {1, …, n^{ck}} written in base n (p.550) → no range bound on the x_i and no condition on n; reason: the argument uses only the totals of each J_{x,ℓ}, which hold for the base-n digits of any x in any base (Nat.ofDigits_digits), so the instances of the source are included
--   - encoding: x_π(ℓ) defined by "d_ℓ = (ℓ−1)3t + t + x_π(ℓ)", d_ℓ the earliest due date in E_ℓ (p.552) → x₀ the least input integer among the jobs of E_ℓ; reason: the due date ℓ·3t + t + x is increasing in x, so the job of earliest due date carries the least x
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), Lemma 8, p.552 (PDF p.8)

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **Lemma 8** (Hermelin, Mnich & Omlor, J. Scheduling 27 (2024), p.552, PDF p.8; corrected
assumption). Let `xs` be a duplicate-free list of positive integers, each smaller than `t`, and
let `σ` be a feasible schedule of the constructed instance. Let `x_{π(ℓ)}` be the least input
integer among the jobs of `E_ℓ` (so `E_ℓ ≠ ∅`). Then
1. `p(E_ℓ) ≤ x_{π(ℓ)}`;
2. `w(E_ℓ) ≤ S·(p(E_ℓ) + 1)`, with equality if and only if `E_ℓ = J_{π(ℓ),ℓ}`.

**Formalization Note.** Weights are scaled by `S = ∏ x_i`. -/
theorem lemma_8 (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (hpos : ∀ a ∈ xs, 1 ≤ a)
    (hlt : ∀ a ∈ xs, a < t) (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) (ℓ x₀ : ℕ)
    (hx₀ : ∃ j ∈ earlyType σ ℓ, (labelOf xs t k L j).value? = some x₀)
    (hmin : ∀ j ∈ earlyType σ ℓ, ∀ x, (labelOf xs t k L j).value? = some x → x₀ ≤ x) :
    pSum (earlyType σ ℓ) ≤ x₀ ∧
      wSum (earlyType σ ℓ) ≤ xs.prod * (pSum (earlyType σ ℓ) + 1) ∧
      (wSum (earlyType σ ℓ) = xs.prod * (pSum (earlyType σ ℓ) + 1) ↔
        earlyType σ ℓ = gadgetSet xs t k L ℓ x₀) := by sorry

end SerialBatchTardy
