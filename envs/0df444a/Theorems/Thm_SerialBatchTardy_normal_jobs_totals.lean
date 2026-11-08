-- Prove2me | Theorems.Thm_SerialBatchTardy_normal_jobs_totals
-- name    : SerialBatchTardy.normal_jobs_totals
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:53:52.506506+00:00
-- url     : https://prove2.me/theorems/d18bef90-01d3-447d-bfba-68cd9aba8b62
-- title:
--   Total processing time and weight of $J_{x,\ell}$
-- statement:
--   Let $x_1,\dots,x_n$ be distinct, $x=x_i$ one of them and $\ell\in\{0,\dots,k-1\}$. In the constructed instance the set $J_{x,\ell}$ satisfies
--
--   $$p(J_{x,\ell})=x,\qquad w(J_{x,\ell})=S\,(x+1),\qquad S=\prod_i x_i.$$
--
--   These two totals drive the correctness of the reduction.
--
--   Differences from the source:
--   - encoding: weights n^h + n^h/x_i and k(X + n), bound kX − t + (n − 1)k → all multiplied by S = ∏ x_i (weights n^h·(S + S/x_i) and S·k(X + n); bound S·(k(X + n) − (t + k)) in ℤ); reason: p.551 makes the weights integral exactly this way ("multiplying them with ∏ x_i"); the comparison is in ℤ so that no truncated subtraction occurs
--   - encoding: ℓ ∈ {1, …, k}, release date (ℓ − 1)3t → ℓ ∈ {0, …, k − 1}, release date ℓ·3t; reason: 0-based indices
--   - generalization: x_i ∈ {1, …, n^{ck}}, base-n representation (n ≥ 2) → any entry x of a duplicate-free list, any n; reason: the base-n digits of x sum back to x for every base (Nat.ofDigits_digits), so the source's case is included
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), §4, p.551 (PDF p.7), "Observe that the total processing time of all jobs in the set J_{x(i),ℓ} is precisely x_i"

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **Totals of a gadget set.** In the constructed instance, for an input integer `x` of the
duplicate-free list `xs` and a gadget index `ℓ < k`, the jobs of `J_{x,ℓ}` have total processing
time `x` and total weight `S·(x + 1)`, where `S = ∏ x_i` is the weight scaling. Hermelin, Mnich &
Omlor, J. Scheduling 27 (2024), §4, p.551 (PDF p.7): "Observe that the total processing time of all
jobs in the set J_{x(i),ℓ} is precisely x_i, and their total weight is x_i + 1."

**Formalization Note.** Weights are scaled by `S`; `ℓ` is 0-based. -/
theorem normal_jobs_totals (xs : List ℕ) (t k : ℕ) (L : List ℕ) (hnd : xs.Nodup) (x : ℕ)
    (hx : x ∈ xs) (ℓ : ℕ) (hℓ : ℓ < k) :
    pSum (gadgetSet xs t k L ℓ x) = x ∧ wSum (gadgetSet xs t k L ℓ x) = xs.prod * (x + 1) := by sorry

end SerialBatchTardy
