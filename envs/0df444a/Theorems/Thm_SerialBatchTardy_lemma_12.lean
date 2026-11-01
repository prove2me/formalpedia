-- Prove2me | Theorems.Thm_SerialBatchTardy_lemma_12
-- name    : SerialBatchTardy.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:53.763161+00:00
-- url     : https://prove2.me/theorems/a7c384f0-16dd-4c9e-a59e-5846bdd4b3f7
-- title:
--   Lemma 12 — time reversal exchanges $\#r$ and $\#d$
-- statement:
--   For every instance $I$ of $1|\text{s-batch}(\infty),r_j|\sum w_jU_j$, the reversed instance $I'$ (release dates $-d_j$, due dates $-r_j$, all else unchanged) satisfies
--
--   1. $\#r(I')=\#d(I)$ and $\#d(I')=\#r(I)$;
--   2. $\#p(I')=\#p(I)$ and $\#w(I')=\#w(I)$;
--   3. for every $W\in\mathbb N$, $I$ has a feasible schedule with $\sum_jw_jU_j\le W$ if and only if $I'$ has one.
--
--   In particular $I$ and $I'$ have the same optimal objective value.
--
--   Differences from the source:
--   - encoding: "can be transformed into an instance … which has the same objective value" → the explicit reversal of the proof, and equality of the sets of achievable thresholds W; reason: the same objective value is the same optimum, which is what the threshold equivalence says
--   - generalization: release and due date counts exchanged → also #p and #w preserved; reason: extra conclusions, used by Corollaries 1 and 2
--   - reading: "S_{B′} ∉ [S_B, C_B) for any batch B′ ≠ B" (p.546), "no two batches are processed at the same time" (p.548) → for distinct used batches, C_B ≤ S_{B′} or C_{B′} ≤ S_B; reason: the two agree for batches of positive length; they differ only when a batch of length 0 (Δ = 0, all its p_j = 0) starts together with another batch, where the literal p.546 condition breaks the time reversal of Lemma 12 (Δ = 0, jobs (p, r, d) = (0, 0, 0) and (1, 0, 1): cost > 0, reversed cost 0)
--   - encoding: start times S_B (domain not stated) → start times in ℤ; reason: all data are integers; rounding every start time down keeps a schedule feasible and keeps every early job early
--   - reading: "integer processing time p_j", "integer batch setup time Δ", integer r_j, d_j (§2, p.548); p_j, w_j, d_j, r_j ∈ ℕ (§1, p.545–546) → p, w, Δ ∈ ℕ (weights positive in the language), r, d ∈ ℤ; reason: the two sections differ; a negative processing or setup time has no meaning, and integer dates are the more general of the two readings (Lemma 12 needs negative dates)
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), Lemma 12, p.553 (PDF p.9)

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **Lemma 12, time reversal** (Hermelin, Mnich & Omlor, J. Scheduling 27 (2024), p.553, PDF p.9).
For every instance `I`, the reversed instance (release date `−d_j`, due date `−r_j`, same processing
times, weights and setup time) has as many distinct release dates as `I` has due dates and as many
distinct due dates as `I` has release dates, the same numbers of distinct processing times and
weights, and the same optimal objective value: for every `W`, `I` has a feasible schedule with
weighted number of tardy jobs at most `W` iff the reversed instance has one. -/
theorem lemma_12 (I : Instance) :
    numR (reverseInstance I) = numD I ∧ numD (reverseInstance I) = numR I ∧
      numP (reverseInstance I) = numP I ∧ numW (reverseInstance I) = numW I ∧
      ∀ W : ℕ, (∃ σ : Schedule I, σ.Feasible ∧ σ.tardyWeight ≤ W) ↔
        (∃ σ' : Schedule (reverseInstance I), σ'.Feasible ∧ σ'.tardyWeight ≤ W) := by sorry

end SerialBatchTardy
