-- Prove2me | Theorems.Thm_SerialBatchTardy_lemma_5
-- name    : SerialBatchTardy.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:41.916398+00:00
-- url     : https://prove2.me/theorems/1ca049d8-142e-4480-94b6-6e01187ae481
-- title:
--   Lemma 5 — a k-Sum solution gives a schedule within the bound
-- statement:
--   Let $x_1,\dots,x_n$ be distinct positive integers and suppose $\sum_{\ell=0}^{k-1}x_{\pi(\ell)}=t$ for some $\pi:\{0,\dots,k-1\}\to\{1,\dots,n\}$. Let the leftover list $L$ split into parts $L_0,\dots,L_{k-1}$ with
--
--   $$\textstyle\sum L_\ell + x_{\pi(\ell)} = t\qquad(\ell<k).$$
--
--   Then the constructed instance has a feasible schedule with $\sum_jw_jU_j\le S\,(kX-t+(n-1)k)$.
--
--   This is the forward direction of the reduction.
--
--   Differences from the source:
--   - generalization: (k − 1)t leftover jobs of processing time 1 → an arbitrary list L of leftover processing times (each leftover job keeps weight S·k(X+n), release 0, due date 3kt); reason: L = List.replicate ((k−1)t) 1 satisfies every hypothesis placed on L, so the printed lemma is the special case
--   - generalization: standing assumption (k − 1)·max x_i < t (p.550) → not assumed; reason: the lemma holds without it
--   - encoding: weights n^h + n^h/x_i and k(X + n), bound kX − t + (n − 1)k → all multiplied by S = ∏ x_i (weights n^h·(S + S/x_i) and S·k(X + n); bound S·(k(X + n) − (t + k)) in ℤ); reason: p.551 makes the weights integral exactly this way ("multiplying them with ∏ x_i"); the comparison is in ℤ so that no truncated subtraction occurs
--   - encoding: ℓ ∈ {1, …, k}, release date (ℓ − 1)3t → ℓ ∈ {0, …, k − 1}, release date ℓ·3t; reason: 0-based indices
--   - reading: "S_{B′} ∉ [S_B, C_B) for any batch B′ ≠ B" (p.546), "no two batches are processed at the same time" (p.548) → for distinct used batches, C_B ≤ S_{B′} or C_{B′} ≤ S_B; reason: the two agree for batches of positive length; they differ only when a batch of length 0 (Δ = 0, all its p_j = 0) starts together with another batch, where the literal p.546 condition breaks the time reversal of Lemma 12 (Δ = 0, jobs (p, r, d) = (0, 0, 0) and (1, 0, 1): cost > 0, reversed cost 0)
--   - encoding: start times S_B (domain not stated) → start times in ℤ; reason: all data are integers; rounding every start time down keeps a schedule feasible and keeps every early job early
--   - generalization: x_i ∈ {1, …, n^{ck}} written in base n (p.550) → no range bound on the x_i and no condition on n; reason: the argument uses only the totals of each J_{x,ℓ}, which hold for the base-n digits of any x in any base (Nat.ofDigits_digits), so the instances of the source are included
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), Lemma 5, p.551 (PDF p.7)

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **Lemma 5** (Hermelin, Mnich & Omlor, J. Scheduling 27 (2024), p.551, PDF p.7). Let `xs` be a
duplicate-free list of positive integers and suppose that `x_{π(0)} + ⋯ + x_{π(k−1)} = t` for some
`π : {0, …, k−1} → {0, …, n−1}`. Let the leftover list `L` split into `k` parts, the `ℓ`-th of sum
`t − x_{π(ℓ)}`. Then the constructed instance has a feasible schedule whose weighted number of
tardy jobs is at most the bound `S·(kX − t + (n − 1)k)`.

**Formalization Note.** For `L = List.replicate ((k-1)*t) 1` the split exists whenever the
`x_{π(ℓ)} ≤ t`, so this is the printed lemma. Weights and bound are scaled by `S = ∏ x_i`. -/
theorem lemma_5 (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (hpos : ∀ a ∈ xs, 1 ≤ a)
    (π : Fin k → Fin xs.length) (hπ : ∑ ℓ, xs.get (π ℓ) = t)
    (a : Fin L.length → Fin k)
    (ha : ∀ ℓ, (∑ i ∈ Finset.univ.filter (fun i => a i = ℓ), L.get i) + xs.get (π ℓ) = t) :
    ∃ σ : Schedule (hardInstance xs t k L), σ.Feasible ∧ (σ.tardyWeight : ℤ) ≤ hardBound xs t k := by sorry

end SerialBatchTardy
