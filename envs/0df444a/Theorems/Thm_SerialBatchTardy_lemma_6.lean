-- Prove2me | Theorems.Thm_SerialBatchTardy_lemma_6
-- name    : SerialBatchTardy.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:46.309494+00:00
-- url     : https://prove2.me/theorems/a87acef7-700e-4eb1-b220-f55078956080
-- title:
--   Lemma 6 — tardy jobs in one last batch, no tardy leftover job
-- statement:
--   Let $x_1,\dots,x_n$ be positive and $k\ge1$. If the constructed instance has a feasible schedule with $\sum_jw_jU_j$ at most the bound $S\,(kX-t+(n-1)k)$, then it has a feasible schedule within the bound and a batch $B^*$ that starts after every other batch completes, such that
--
--   1. a job is tardy if and only if it lies in $B^*$, and no leftover job is tardy;
--   2. the early normal jobs have total weight at least $S\,(t+k)$.
--
--   This normal form is the entry point of the converse direction.
--
--   Differences from the source:
--   - generalization: (k − 1)t leftover jobs of processing time 1 → an arbitrary list L of leftover processing times (each leftover job keeps weight S·k(X+n), release 0, due date 3kt); reason: L = List.replicate ((k−1)t) 1 satisfies every hypothesis placed on L, so the printed lemma is the special case
--   - generalization: the standing assumption (k − 1)·max x_i < t and distinct x_i → positive x_i only; reason: the lemma holds without them
--   - reading: k (the k-Sum parameter; k ≥ 1 implicit) → 1 ≤ k; reason: k-Sum asks for k integers; at k = 0 with no x_i a leftover job of positive length may be tardy at weight 0
--   - encoding: batches B_1, …, B_b, B_{b+1} scheduled in that order → a batch label b* that starts after every other used batch completes (b* may be empty); reason: same content; batches are labels
--   - encoding: weights n^h + n^h/x_i and k(X + n), bound kX − t + (n − 1)k → all multiplied by S = ∏ x_i (weights n^h·(S + S/x_i) and S·k(X + n); bound S·(k(X + n) − (t + k)) in ℤ); reason: p.551 makes the weights integral exactly this way ("multiplying them with ∏ x_i"); the comparison is in ℤ so that no truncated subtraction occurs
--   - reading: "S_{B′} ∉ [S_B, C_B) for any batch B′ ≠ B" (p.546), "no two batches are processed at the same time" (p.548) → for distinct used batches, C_B ≤ S_{B′} or C_{B′} ≤ S_B; reason: the two agree for batches of positive length; they differ only when a batch of length 0 (Δ = 0, all its p_j = 0) starts together with another batch, where the literal p.546 condition breaks the time reversal of Lemma 12 (Δ = 0, jobs (p, r, d) = (0, 0, 0) and (1, 0, 1): cost > 0, reversed cost 0)
--   - encoding: start times S_B (domain not stated) → start times in ℤ; reason: all data are integers; rounding every start time down keeps a schedule feasible and keeps every early job early
--   - generalization: x_i ∈ {1, …, n^{ck}} written in base n (p.550) → no range bound on the x_i and no condition on n; reason: the argument uses only the totals of each J_{x,ℓ}, which hold for the base-n digits of any x in any base (Nat.ofDigits_digits), so the instances of the source are included
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), Lemma 6, p.551 (PDF p.7)

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **Lemma 6** (Hermelin, Mnich & Omlor, J. Scheduling 27 (2024), p.551, PDF p.7). Let the input
integers be positive and `k ≥ 1`. If the constructed instance has a feasible schedule with weighted
number of tardy jobs at most the bound, then it has one, also within the bound, with a batch `b*`
that starts after every other used batch completes, such that
1. a job is tardy if and only if it is in `b*`, and no leftover job is tardy;
2. the early normal jobs have total weight at least `S·(t + k)`.

**Formalization Note.** Weights and bound are scaled by `S = ∏ x_i`; `b*` may be empty. -/
theorem lemma_6 (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hpos : ∀ a ∈ xs, 1 ≤ a) (hk : 1 ≤ k)
    (σ : Schedule (hardInstance xs t k L)) (hσ : σ.Feasible)
    (hW : (σ.tardyWeight : ℤ) ≤ hardBound xs t k) :
    ∃ σ' : Schedule (hardInstance xs t k L), σ'.Feasible ∧
      (σ'.tardyWeight : ℤ) ≤ hardBound xs t k ∧
      ∃ bstar : ℕ,
        (∀ b, σ'.Used b → b ≠ bstar → σ'.comp b ≤ σ'.start bstar) ∧
        (∀ j, σ'.IsTardy j ↔ σ'.batch j = bstar) ∧
        (∀ j, (labelOf xs t k L j).gadget? = none → ¬ σ'.IsTardy j) ∧
        xs.prod * (t + k) ≤
          ∑ j ∈ Finset.univ.filter
              (fun j => (labelOf xs t k L j).gadget?.isSome ∧ ¬ σ'.IsTardy j),
            ((hardInstance xs t k L).job j).w := by sorry

end SerialBatchTardy
