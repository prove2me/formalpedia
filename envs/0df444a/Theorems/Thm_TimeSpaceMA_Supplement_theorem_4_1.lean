-- Prove2me | Theorems.Thm_TimeSpaceMA_Supplement_theorem_4_1
-- name    : TimeSpaceMA.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:45:37.659867+00:00
-- url     : https://prove2.me/theorems/2fd27561-3639-4c23-a310-23228b7c0466
-- title:
--   Theorem 4.1 — fast MA protocol for one-tape time-$t$ computations
-- statement:
--   Let $L\in\mathrm{TIME}_1[t]$, where $t$ is time-constructible and $t(n)\ge n$. Then for every $\varepsilon>0$, $L$ has a Merlin–Arthur protocol with perfect completeness and soundness at most $1/3$ whose message length and verifier running time are bounded, up to one uniform constant, by
--
--   $$
--   \max\left\{t(n)^{13/14},\,\bigl(t(n)n\bigr)^{1/2}\right\}t(n)^\varepsilon.
--   $$
--
--   Thus a one-work-tape computation of duration $t$ admits a non-interactive proof whose message and verification costs are below $t$ whenever the displayed maximum is sublinear. The theorem asserts no bound on Merlin's running time or on Arthur's randomness.
--
--   **Formalization Note** $\mathrm{TIME}_1$ uses the published random-access-input machine with exactly one sequential work tape. The real bound is rounded up to a natural-number budget; `InMATIME` gives the uniform verifier and protocol guarantees.
--
--   Differences from the source:
--   - encoding: TIME₁[t] and time-constructible are standard machine-independent notions → the published TimeSpaceMA.RATM with exactly one work tape for TIME₁ and a unary-output O(t) clock machine for time constructibility; reason: the page fixes random input access and sequential work-tape access but leaves the standard clock convention implicit
--   - encoding: message length and Arthur's running time are both max{t^{13/14},(tn)^{1/2}}t^ε → their sum is at most C times the ceiling of that bound, with C uniform and chosen after ε; reason: separate bounds and a combined bound differ by only a factor two, and the proof on pp.23–24 absorbs constant and polylogarithmic factors into t^ε
--   - encoding: asymptotic power bound at n = 0 → the natural budget is rounded up and InMATIME uses max{T(0),1}; reason: this removes only the zero-size junk value and changes no positive input length
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Theorem 4.1 (Theorem 1.3, restated), p.23; proof pp.24–25

import Definitions.Def_TimeSpaceMA_Supplement_TimeConstructible
import Definitions.Def_TimeSpaceMA_Supplement_InTIME1
import Definitions.Def_TimeSpaceMA_Supplement_InMATIME

set_option autoImplicit false

namespace TimeSpaceMA
namespace Supplement

/-- **Theorem 4.1 (Theorem 1.3, restated)** (Williams–Xi, *Short Non-Interactive Proofs for
Time-Space Computations*, STOC 2027 submission, manuscript sha256 184c2f95…, p.23).
If `L ∈ TIME₁[t]`, `t` is time-constructible, and `t(n) ≥ n`, then for every `ε > 0`,
`L` has an MA protocol whose message length and Arthur running time are both bounded, up to one
uniform constant, by
`max {t(n)^(13/14), (t(n)n)^(1/2)} t(n)^ε`.

**Formalization Note** `TIME₁` uses the published random-access-input machine with exactly one
sequential work tape. `TimeConstructible` computes the unary clock in linear overhead. The real-valued
displayed bound is rounded up to a natural-number budget, and `InMATIME` supplies perfect
completeness, soundness `1/3`, a uniform verifier, and the combined message-plus-verifier cost.
No Merlin-time or randomness conclusion is added. The maximum with one inside `InMATIME` only
handles the zero-size boundary. -/
theorem theorem_4_1 (L : Set (List Bool)) (t : ℕ → ℕ) (hL : InTIME1 L t)
    (htc : TimeConstructible t) (ht : ∀ n, n ≤ t n) (ε : ℝ) (hε : 0 < ε) :
    InMATIME L (fun n => Nat.ceil
      (max ((t n : ℝ) ^ ((13 : ℝ) / 14))
        (((t n : ℝ) * (n : ℝ)) ^ ((1 : ℝ) / 2)) * (t n : ℝ) ^ ε)) := by sorry

end Supplement
end TimeSpaceMA
