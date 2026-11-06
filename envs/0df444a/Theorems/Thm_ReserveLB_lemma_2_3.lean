-- Prove2me | Theorems.Thm_ReserveLB_lemma_2_3
-- name    : ReserveLB.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:37.800316+00:00
-- url     : https://prove2.me/theorems/87ad7e12-9a4b-43bb-98b0-63be77084929
-- title:
--   Lemma 2.3 — stopped-moment bound for both crossing events
-- statement:
--   Let $X_1, \dots, X_n$ be independent random variables with values in $[0,1]$, $S = \sum_j X_j$, $s \ge 1$, $r \ge 0$, $b \ge 1$ an integer, and
--   $$
--   R = \sum_j \beta_b(X_j/s).
--   $$
--   Then each of the crossing events $H_r = \{S > r\}$ (strict) and $H_r = \{S \ge r\}$ (inclusive) satisfies
--   $$
--   \mathbb P(H_r) \ge b^{-(r+1)/s}\bigl(1 - b^{r/s - R}\bigr).
--   $$
--
--   The bound turns a large total effective size into a lower bound on the probability that the load crosses a level; Lemma 3.1 uses it with $s = 3$ to show that large first and prefix risks are incompatible with a cheap comparator.
--
--   Differences from the source:
--   - reading: either the strict or inclusive crossing event H_r satisfies the bound → both events satisfy it; reason: the proof stops at the first crossing of whichever kind is chosen and works for each; this is the stronger reading
--   - encoding: the crossing event at level r → {S > r} (strict) and {S ≥ r} (inclusive); reason: the summands are nonnegative, so the partial sums increase and some partial sum crosses r exactly when the total does
--   - generalization: integer base b > 1 → integer b ≥ 1; reason: at b = 1 the right side is 1·(1 − 1) = 0 and the bound is trivial; b > 1 is the source's case
--   - encoding: independent X_j ∈ [0, 1]; β_b → measurable X_j, iIndepFun, 0 ≤ X_j ω ≤ 1 for every ω; StochLoadBal.Makespan.effSize; reason: as for (2); same instances
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.3, p.4

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

open MeasureTheory ProbabilityTheory

namespace ReserveLB

/-- **Lemma 2.3 — stopped-moment bound.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.3, p.4: "For independent Xj ∈ [0, 1], S = Σ_j Xj, R = Σ_j βb(Xj/s), s ≥ 1, and
r ≥ 0, either the strict or inclusive crossing event Hr at level r satisfies
P(Hr) ≥ b^(−(r+1)/s)(1 − b^(r/s−R))."

Let `X_1, …, X_n` be independent random variables with values in `[0, 1]`, `S = Σ_j X_j`,
`b ≥ 1` an integer, `s ≥ 1`, `r ≥ 0`, and `R = Σ_j β_b(X_j/s)`. Then both crossing events,
`{S > r}` (strict) and `{S ≥ r}` (inclusive), have probability at least
`b^(−(r+1)/s) (1 − b^(r/s − R))`.

**Formalization Note.** The summands are nonnegative, so the partial sums increase and the
crossing events at level `r` are `{S > r}` and `{S ≥ r}`. `β_b` is the platform's
`StochLoadBal.Makespan.effSize`. -/
theorem lemma_2_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (hind : iIndepFun X P)
    (hX01 : ∀ j ω, 0 ≤ X j ω ∧ X j ω ≤ 1) (b : ℕ) (hb : 1 ≤ b) (s : ℝ) (hs : 1 ≤ s)
    (r : ℝ) (hr : 0 ≤ r) :
    (b : ℝ) ^ (-(r + 1) / s) *
        (1 - (b : ℝ) ^ (r / s - ∑ j, StochLoadBal.Makespan.effSize P b (fun ω => X j ω / s))) ≤
      P.real {ω | r < ∑ j, X j ω} ∧
    (b : ℝ) ^ (-(r + 1) / s) *
        (1 - (b : ℝ) ^ (r / s - ∑ j, StochLoadBal.Makespan.effSize P b (fun ω => X j ω / s))) ≤
      P.real {ω | r ≤ ∑ j, X j ω} := by sorry

end ReserveLB
