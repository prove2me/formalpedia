-- Prove2me | Theorems.Thm_SchedComplexity_Partition_Supplement_theorem_1k
-- name    : SchedComplexity.Partition.Supplement.theorem_1k
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:42:44.389051+00:00
-- url     : https://prove2.me/theorems/3413488b-7961-48f0-97d2-110d04d10e58
-- title:
--   Theorem 1(k) — absorb the last release date in an added first machine
-- statement:
--   For every fixed $m\ge2$, every $\lambda\subseteq\{w_j=1\}$, and every one of the five criteria $k$,
--
--   $$L(m-1,F,\{r_n\ge0\}\cup\lambda,k)\le_p L(m,F,\lambda,k).$$
--
--   The variable-machine version is also asserted: the source ranges over all positive old counts $m-1$, and the construction outputs one more machine. In particular, $m=2$ has a single-machine source. The explicit data construction `absorbRelease` prepends a first operation with duration $r_j$ to job $j$, shifts all old machine indices and sets every release date to zero; weights and due dates are preserved. Thus all but the last new processing times are zero, as printed. The reduction statement includes polynomial running time and every threshold of the relevant type.
--
--   Differences from the source:
--   - encoding: recognition problems and polynomial-time reducibility with implicit finite input syntax → binary-coded languages over BSym and CookPvsNP polynomial-time many-one reductions; signed integer thresholds for maximum lateness and natural thresholds otherwise; reason: Sections 2–3 specify integer data and recognition questions; this fixes explicit bit syntax and retains negative lateness
--   - reading: the Section 3 family with ℓ specified only for m>1 and nonnegative operation counts → every label at m=1 is the one-operation single-machine problem; variable m ranges over positive counts; an empty operation list has B_j=C_j=0; reason: the single-machine boundary is explicitly included in 1(c),(k); the empty-list convention extends the published shop completion without imposing a new positivity assumption
--   - encoding: m−1 machines on the left, m machines on the right, including variable m → fixed counts satisfy 2≤m before Nat subtraction; the variable source has arbitrary positive old count and absorbRelease outputs old count plus one; reason: this is the same count parameterization; the single-machine source at m=2 is retained and no zero machine count is allowed
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 9, Theorem 1(k)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Family

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

theorem theorem_1k (lam : Parameters) (hweights : lam ⊆ {Feature.unitWeights})
    (k : Criterion) :
    (∀ m : ℕ, 2 ≤ m →
      PolyReducible (language (.fixed (m - 1)) .flow (lam ∪ {Feature.releaseLast}) k)
        (language (.fixed m) .flow lam k)) ∧
    PolyReducible (language .variable .flow (lam ∪ {Feature.releaseLast}) k)
      (language .variable .flow lam k) := by sorry

end SchedComplexity.Partition.Supplement
