-- Prove2me | Theorems.Thm_QuasiPolyTrace_theorem_44_pairwise_to_reconstruction
-- name    : QuasiPolyTrace.theorem_44_pairwise_to_reconstruction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:33:13.04686+00:00
-- url     : https://prove2.me/theorems/cc871c08-70bd-455e-8ba8-9eb3cbe01543
-- title:
--   Proof of Theorem 44, reduction — pairwise tests give reconstruction with $O(n)$ more traces
-- statement:
--   There is a universal constant $C$ such that for every $n\ge1$, every deletion probability $q\in[0,1]$ and every $T$: if every two distinct strings in $\{0,1\}^n$ can be distinguished from $T$ traces, then trace reconstruction of $n$-bit strings succeeds with probability at least $\tfrac23$ from
--
--   $$
--   C\cdot n\cdot T
--   $$
--
--   traces: one algorithm, depending only on $n$, $q$ and the traces, returns every $x$ with probability at least $\tfrac23$.
--
--   This is the standard reduction from reconstruction to pairwise distinguishing quoted in the proof of Theorem 44.
--
--   Differences from the source:
--   - reading: O(n) factor more traces suffice to reconstruct an arbitrary x → C · n · T traces with C universal, for every n ≥ 1, q ∈ [0, 1], T; reason: O(n) is a universal constant times n; "reconstruct" is Definition 2 (success probability 2/3)
-- source:
--   Burudgunte, Valiant, Wang, Quasipolynomial Trace Reconstruction, manuscript of November 2, 2026 (later version of arXiv:2607.04073; sha256 9ecb6d18…), proof of Theorem 44, p.44 ("It is a standard fact…")

import Mathlib
import Definitions.Def_TraceReconstruction
import Definitions.Def_QuasiPolyTrace_Distinguishes

namespace QuasiPolyTrace

open OAI.TraceReconstruction

/-- **Proof of Theorem 44, reduction step (pairwise distinguishing gives reconstruction with O(n) more
traces).** Burudgunte, Valiant, Wang, *Quasipolynomial Trace Reconstruction*, manuscript of November 2, 2026
(later version of arXiv:2607.04073; sha256 9ecb6d18…), proof of Theorem 44, p.44: "It is a standard fact that, if one can distinguish pairs of
traces in a certain sample complexity, then O(n) factor more traces suffice to reconstruct an arbitrary
x, and we can increase c to encompass this small extra factor."

Statement: there is a universal constant `C` such that for every `n ≥ 1`, every deletion probability
`q ∈ [0, 1]` and every `T`: if every pair of distinct `n`-bit strings can be distinguished from `T`
traces (`Distinguishes`), then `C · n · T` traces suffice for trace reconstruction with success
probability `2/3` (`SufficientBudget` of the reused block `OAI.TraceReconstruction`).

**Formalization Note.**
* "O(n) factor" is `C · n` with `C` universal, chosen before `n`, `q` and `T`.
* The reused block's `q` is the deletion probability (retention probability `1 − q`).
* The reconstruction algorithm may depend on `n`, `q` and `T` (Definition 2 lets it), never on the
  unknown string. -/
theorem theorem_44_pairwise_to_reconstruction :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ T : ℕ,
      (∀ x y : Word n, x ≠ y → Distinguishes n q T x y) →
      SufficientBudget n q (2 / 3) (C * n * T) := by sorry

end QuasiPolyTrace
