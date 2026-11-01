-- Prove2me | Theorems.Thm_SerialBatchTardy_leftoverList_spec
-- name    : SerialBatchTardy.leftoverList_spec
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:53:49.864768+00:00
-- url     : https://prove2.me/theorems/e3190666-09f3-49bf-8743-30c835e9f922
-- title:
--   The leftover list: sum $(k-1)t$, $O(kn\log t)$ entries, every split
-- statement:
--   Let $n,k,t\ge2$ and let $L=L(n,k,t)$ be the leftover list. Then
--
--   1. every entry of $L$ is $n^h$ for some $h\le\lfloor\log_n t\rfloor$;
--   2. the entries of $L$ sum to $(k-1)t$;
--   3. $L$ has at most $2(k+1)\,n\,(\lfloor\log_n t\rfloor+1)$ entries;
--   4. for all $s_0,\dots,s_{k-1}\in\mathbb N$ with $\sum_\ell s_\ell=(k-1)t$, the entries of $L$ can be distributed into $k$ parts with sums $s_0,\dots,s_{k-1}$.
--
--   With this list in place of $(k-1)t$ unit jobs, the constructed instance has polynomially many jobs and still $O(k)$ distinct processing times.
--
--   Differences from the source:
--   - reading: (k − 1)t identical leftover jobs of processing time 1 → the list L(n, k, t) of powers of n with the same total (k − 1)t, O(kn log t) entries, splitting into any k parts of the needed sums; reason: t can be as large as k·n^{3ck}, so (k − 1)t unit jobs cannot be written down in f(k)·n^{O(1)} time on the job-list input of §2; the proof step is repaired, the theorem it serves is unchanged
-- source:
--   Hermelin, Mnich & Omlor, Serial batching to minimize the weighted number of tardy jobs, J. Scheduling 27 (2024), §4, p.551 (PDF p.7), the leftover jobs ("We create (k − 1)t identical jobs, called leftover jobs"); repaired, see the mission's moderation notes

import Definitions.Def_SerialBatchTardy_Construction
set_option autoImplicit false

namespace SerialBatchTardy

/-- **The leftover list.** For `n, k, t ≥ 2`, the list `leftoverList n k t` consists of powers
`n^h` with `h ≤ ⌊log_n t⌋`, has sum `(k − 1)t` and at most `2(k + 1)n(⌊log_n t⌋ + 1)` entries,
and for every `s_0, …, s_{k−1}` with `∑ s_ℓ = (k − 1)t` its entries can be distributed into `k`
parts with sums `s_0, …, s_{k−1}`.

It replaces the `(k − 1)t` unit leftover jobs of Hermelin, Mnich & Omlor, J. Scheduling 27 (2024),
§4, p.551 (PDF p.7): "We create (k − 1)t identical jobs, called leftover jobs, each with the
following parameters: Processing time 1 …". -/
theorem leftoverList_spec (n k t : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (ht : 2 ≤ t) :
    (∀ e ∈ leftoverList n k t, ∃ h ≤ Nat.log n t, e = n ^ h) ∧
      (leftoverList n k t).sum = (k - 1) * t ∧
      (leftoverList n k t).length ≤ 2 * (k + 1) * n * (Nat.log n t + 1) ∧
      ∀ s : Fin k → ℕ, ∑ ℓ, s ℓ = (k - 1) * t →
        ∃ a : Fin (leftoverList n k t).length → Fin k,
          ∀ ℓ, ∑ i ∈ Finset.univ.filter (fun i => a i = ℓ), (leftoverList n k t).get i = s ℓ := by sorry

end SerialBatchTardy
