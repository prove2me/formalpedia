-- Prove2me | Theorems.Thm_SublinearChoresMMS_Disposal_lemma_3_1_rearrangement
-- name    : SublinearChoresMMS.Disposal.lemma_3_1_rearrangement
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T10:32:47.704849+00:00
-- url     : https://prove2.me/theorems/70a1f226-8b8e-4a11-b214-aa88825306dd
-- title:
--   Lemma 3.1, Appendix A.1.3 — a valid packing can be rearranged into O(L³) segments with O(√L) more exclusions
-- statement:
--   The overview of the proof of Lemma 3.1 (Appendix A.1, printed p. 20) describes the second stage: "in Appendix A.1.3, we rearrange this packing via a minimum-cost linear program and cycle rounding so that the bin and exclusion labels change at most $O(L^3)$ times along the representative order, while excluding at most $O(\sqrt{L})$ additional representatives." Appendix A.1.3 (printed pp. 24–26) carries this out. This statement formalizes that stage for an arbitrary valid packing. Together with the halving stage (Lemma A.2, `SublinearChoresMMS.Disposal.lemma_a_2`), it gives `SublinearChoresMMS.Disposal.lemma_3_1`.
--
--   **Statement.** There are $A, B > 0$ and $n_0 \ge 2$ with the following property. Let $n \ge n_0$, $q$ = `blockSize n` $= 2^{\lfloor \log_2 \sqrt{n \ln n}\rfloor}$ and $L = \lfloor n/q \rfloor$. Let $q \le m$ with $q \mid m$, let the costs $c$ be `Normalized` (positive, strictly decreasing in the chore index, $\mu_i = 1$), and fix an agent $i$. Then every labelling $p$ of the representatives that is a `ValidPacking` for agent $i$ can be replaced by another `ValidPacking` $p'$ for agent $i$ such that:
--   - `excludedCount p'` $\le$ `excludedCount p` $+ A\sqrt{L}$;
--   - `segments p'` $\le B\,(L^3 + $ `excludedCount p`$)$.
--
--   Here a labelling sends representative $r$ to a bin among the $L$ unit bins and the extra bin of capacity $(n \bmod q)/q$, or excludes it. Validity means that representative 1 (block 0) is excluded and that every bin's representative cost is at most its capacity. `segments` counts the label changes along representatives $2, \dots, m/q$, exclusion included.
--
--   The paper's count, "Including the $M_\ell + 2d$ representatives excluded before rounding, the total number of segments is $O(d \cdot b^2 + \sqrt{L}) = O(L^3)$" (printed p. 26), adds the exclusions already present in the input. For an input with $O(\sqrt L)$ exclusions, which is what the halving stage produces, the bound $B(L^3 + \text{excludedCount } p)$ is $O(L^3)$.
--
--   **Route (the paper's).** The proof runs in five steps:
--   1. Exclude up to $2d$ of the costliest representatives, where $d = \lceil\sqrt b\rceil$ and $b$ is the number of bins, to create slack.
--   2. Split the remaining costs into $d$ ranges of width $\kappa/d$. Keep $b(b-1)$ of the cheapest representatives of each range fixed. Take an optimal basic solution of the linear program that minimizes $\sum_{v,a} v\,a^2 z_{v,a}$ subject to the supply, per-range count and bin-load constraints. Optimality forbids two bins from alternating along four increasing costs of one range.
--   3. Round with the cycle-rounding of Ageev–Sviridenko; at most $b-1$ updates are needed.
--   4. Repair the bins by swaps with fixed representatives and a greedy repacking of the bins in $V$, which costs $O(d)$ further exclusions.
--   5. Count the segments: $O(d\,b^2)$ boundaries come from the movable representatives, the fixed ones and the swaps.
-- source:
--   Lin, Wu, Zhou, Best-of-Many-Worlds MMS Allocation for Chores with Sublinear Disposals (STOC 2027 submission 845), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf, pp. 24–26, Appendix A.1.3, proof of Lemma 3.1, rearranging the packing into few segments (printed pp. 24–26 / PDF pp. 25–27; announced on printed p. 20)

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Packing

noncomputable section

namespace SublinearChoresMMS.Disposal

theorem lemma_3_1_rearrangement :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ m : ℕ,
        blockSize n ≤ m → blockSize n ∣ m →
        ∀ c : Cost n m, Normalized c → ∀ i : Fin n,
          ∀ p : Labels n m (blockSize n), ValidPacking c i p →
          ∃ p' : Labels n m (blockSize n), ValidPacking c i p' ∧
            (excludedCount p' : ℝ) ≤ excludedCount p + A * Real.sqrt (n / blockSize n : ℕ) ∧
            (segments p' : ℝ) ≤ B * ((n / blockSize n : ℕ) ^ 3 + excludedCount p) := by
  sorry

end SublinearChoresMMS.Disposal
