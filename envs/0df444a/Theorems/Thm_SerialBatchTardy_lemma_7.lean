-- Prove2me | Theorems.Thm_SerialBatchTardy_lemma_7
-- name    : SerialBatchTardy.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:50.889443+00:00
-- url     : https://prove2.me/theorems/4d624a4a-264a-4ae4-adf4-946a21cb59a5
-- title:
--   Lemma 7 — the early jobs of type $\ell$ lie in one batch (corrected: $x_i < t$)
-- statement:
--   Let every $x_i$ be smaller than $t$, and let $\sigma$ be a feasible schedule of the constructed instance. For every $\ell$ with $E_\ell\ne\emptyset$ there is a unique batch $B(\ell)$ with $E_\ell\subseteq B(\ell)$, and $B(\ell)$ contains no job of $E_{\ell'}$ for $\ell'\ne\ell$.
--
--   This attaches one batch to each type of early normal jobs.
--
--   Differences from the source:
--   - correction: standing assumption "k − 1 times the largest integer in {x_1, …, x_n} is less than t" (p.550) → every x_i < t; reason: at k = 1 the printed assumption only says 0 < t and Lemma 7 is false: k = 1, t = 2, xs = (5, 100), n = 2; J_{5} = jobs of length 1, 4 (due 7), J_{100} = jobs 4, 32, 64 (due 102); batches [0, 7) with the jobs 1, 4 of J_5 and [7, 73) with the job 64 of J_100 make all three early; for k ≥ 2 the printed assumption implies x_i < t, so every k ≥ 2 instance of the source is covered (the proof itself uses "all x_i are smaller than t", p.551)
--   - generalization: the schedule of Lemma 6 (within the bound) → every feasible schedule, any leftover list L; reason: the lemma uses only feasibility
--   - generalization: "there is a unique batch B(ℓ) … with E_ℓ ⊆ B" → also: B(ℓ) contains no job of E_{ℓ′}, ℓ′ ≠ ℓ; reason: an extra conclusion, stated in the proof
--   - encoding: ℓ ∈ {1, …, k}, release date (ℓ − 1)3t → ℓ ∈ {0, …, k − 1}, release date ℓ·3t; reason: 0-based indices
--   - reading: "S_{B′} ∉ [S_B, C_B) for any batch B′ ≠ B" (p.546), "no two batches are processed at the same time" (p.548) → for distinct used batches, C_B ≤ S_{B′} or C_{B′} ≤ S_B; reason: the two agree for batches of positive length; they differ only when a batch of length 0 (Δ = 0, all its p_j = 0) starts together with another batch, where the literal p.546 condition breaks the time reversal of Lemma 12 (Δ = 0, jobs (p, r, d) = (0, 0, 0) and (1, 0, 1): cost > 0, reversed cost 0)
--   - encoding: start times S_B (domain not stated) → start times in ℤ; reason: all data are integers; rounding every start time down keeps a schedule feasible and keeps every early job early
--   - generalization: distinct x_i ∈ {1, …, n^{ck}} written in base n (p.550) → no distinctness, positivity, range bound or condition on n (only x_i < t); reason: the argument uses only release and due dates and the setup time, so the instances of the source are included
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), Lemma 7, p.551 (PDF p.7)

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **Lemma 7** (Hermelin, Mnich & Omlor, J. Scheduling 27 (2024), p.551, PDF p.7; corrected
assumption). Suppose every input integer is smaller than `t`. In every feasible schedule of the
constructed instance, if the set `E_ℓ` of early normal jobs of type `ℓ` is nonempty, then there is a
unique batch containing all of `E_ℓ`, and that batch contains no job of `E_{ℓ'}` for `ℓ' ≠ ℓ`. -/
theorem lemma_7 (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hlt : ∀ a ∈ xs, a < t)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible) (ℓ : ℕ)
    (hE : (earlyType σ ℓ).Nonempty) :
    ∃! b : ℕ, (∀ j ∈ earlyType σ ℓ, σ.batch j = b) ∧
      ∀ ℓ' : ℕ, ℓ' ≠ ℓ → ∀ j ∈ earlyType σ ℓ', σ.batch j ≠ b := by sorry

end SerialBatchTardy
