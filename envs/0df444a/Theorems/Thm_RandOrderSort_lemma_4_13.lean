-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_13
-- name    : RandOrderSort.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:57.031072+00:00
-- url     : https://prove2.me/theorems/312f8f30-7e3a-45c5-adba-a15d1c23b327
-- title:
--   Lemma 4.13 — conditional product for the future blocks
-- statement:
--   There are absolute constants $\theta_s>0$ and $M_s\ge 1$ such that, for $n\ge 8192$ and $q\in(0,1)$,
--   $$\mathbb E\Bigl[\exp\Bigl(\theta_s\sum_{i=1}^{k-1}W_i\Bigr)\Bigm|P_L\Bigr]\le M_s^{k-1}.$$
--
--   Each $W_i$ depends only on $P_L$ and the phase-$i$ input block, so the bound does not need the distribution of the surviving empty cells.
--
--   Differences from the source:
--   - generalization: conditioning on P_L in the i.i.d. experiment → every fixed vector y of the first m inputs, the other N inputs i.i.d. uniform, with integrability stated; reason: the conditional law given the prefix is this product measure, and the Lean covers every y
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.13, p.35, display (51)

import Mathlib
import Definitions.Def_RandOrderSort_Wi
open MeasureTheory

namespace RandOrderSort

/-- **Lemma 4.13 (Conditional product for the future blocks)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.35: "There are absolute
constants θ_s > 0 and M_s ≥ 1 such that E[exp(θ_s ∑_{i=1}^{k−1} W_i) | P_L] ≤ M_s^{k−1}. (51)"

**Formalization Note.** `θ_s`, `M_s` are chosen before `n`, `q` and the conditioning. Conditioning
on `P_L` is fixing a realization `y` of the first `m` inputs, the other `N` inputs `w` being i.i.d.
`U[0,1]`; `W_i` is (50). -/
theorem lemma_4_13 :
    ∃ θs : ℝ, 0 < θs ∧ ∃ Ms' : ℝ, 1 ≤ Ms' ∧ ∀ n, 16 * T ≤ n → ∀ q : ℝ, 0 < q → q < 1 →
      ∀ y : Fin (m n) → ℝ,
        Integrable (fun w : Fin (N n) → ℝ => Real.exp (θs * WSum (joinIn y w) q)) (iidUnif (N n)) ∧
        ∫ w, Real.exp (θs * WSum (joinIn y w) q) ∂(iidUnif (N n)) ≤ Ms' ^ (k n - 1) := by sorry

end RandOrderSort
