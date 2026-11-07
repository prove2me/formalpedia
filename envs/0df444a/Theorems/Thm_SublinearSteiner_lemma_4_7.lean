-- Prove2me | Theorems.Thm_SublinearSteiner_lemma_4_7
-- name    : SublinearSteiner.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:17.15673+00:00
-- url     : https://prove2.me/theorems/a807946f-5dbb-4e63-bd93-70af1012e0e5
-- title:
--   Lemma 4.7 — band completeness, (4.11)
-- statement:
--   Let $B_Q=\lceil400\mathcal A\rceil$ and $T_Q=\sum_i\sum_{C\in\mathcal C_i,\ |C|\le B_Q}D_i(C)$. On the cover event, that is, when each $N_i$ is a $\delta a_i$-cover of $T$ and $\sum_ia_ig_i\le\mathcal AL$,
--   $$T_Q\le Q_Q(L-\mathrm{OPT}).$$
--   Moreover, with probability at least $1-10^{-4}$ over the shift $\Theta$ of the grid $a_i=a_0\Theta\omega^i$,
--   $$\Lambda\le2T_Q/\sigma_0+L/100.$$
--
--   So the observable $T_Q$ controls the ideal statistic $\Lambda$ on the same grid.
--
--   Differences from the source:
--   - generalization: the A of (4.9) and the grid (4.2) → any A > 0 and any a₀ > 0; reason: the proof uses only Σ a_i g_i ≤ AL; (4.2) is the case a₀ = λ_f ω^{−q₀}
--   - reading: with probability at least 1 − 10⁻⁴ over the shift → the set of Θ for which some family of covers on the cover event violates (4.11) has measure at most 10⁻⁴; reason: the page’s bad event depends only on T and the shift, so the bound holds for all covers at once
--   - generalization: the floored metric of p.19 ("From now on we work with the floored metric") → any metric w on Fin n, with its own L and OPT; reason: the proof uses no property of the flooring; the floored metric is a metric (SublinearSteiner.floored), so the statement specializes to it
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.7, (4.11), p.24, with (4.9), p.23

import Mathlib
import Definitions.Def_SublinearSteiner_Statistics
import Definitions.Def_SublinearSteiner_Estimator

namespace SublinearSteiner

/-- Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027 submission (manuscript sha256 ae133037…), Lemma 4.7 (Band completeness), (4.11), p.24. Let `B_Q = ⌈400A⌉` and `T_Q = Σ_i Σ_{C ∈ C_i, |C| ≤ B_Q} D_i(C)`. On the cover
event, `T_Q ≤ Q_Q (L − OPT)`. Moreover, with probability at least `1 − 10⁻⁴` over the shift of the grid,
`Λ ≤ 2T_Q/σ0 + L/100`.

**Formalization Note.**
* The grid is `a_i = a₀ Θ ω^i`, `0 ≤ i < I`, which contains (4.2). `Λ` is summed over it.
* The cover event: each `N_i` is a `ρ_i`-cover with `ρ_i = δa_i`, and `Σ_i a_i g_i ≤ AL` (4.9).
* `A > 0` is arbitrary; the page's `A` is one value.
* The probability bound holds for all covers simultaneously: the outer measure of the set of `Θ` for which some family of
  covers on the cover event violates (4.11) is at most `10⁻⁴`. The page's bad event depends only on `T` and the shift. -/
theorem lemma_4_7 {n : ℕ} (w : FinMetric n) (T : Finset (Fin n)) (OPT L : ℝ)
    (hOPT : IsSteinerOpt T w OPT) (hL : IsTerminalMST T w L) (A : ℝ) (hA : 0 < A) (QQ : ℕ)
    (hQQ : omega ^ (-(QQ : ℤ)) < tau / 2) (a₀ : ℝ) (ha₀ : 0 < a₀) (I : ℕ) :
    (∀ Θ : ℝ, 1 ≤ Θ → Θ < omega → ∀ N : ℕ → Finset (Fin n),
      (∀ i < I, IsCover w T (N i) (delta * shiftGrid a₀ Θ i)) →
      ∑ i ∈ Finset.range I, shiftGrid a₀ Θ i * ((N i).card : ℝ) ≤ A * L →
      boundedBandSum w N (shiftGrid a₀ Θ) I (bandCap A) ≤ QQ * (L - OPT)) ∧
    shiftLaw {Θ : ℝ | ∃ N : ℕ → Finset (Fin n),
      (∀ i < I, IsCover w T (N i) (delta * shiftGrid a₀ Θ i)) ∧
      ∑ i ∈ Finset.range I, shiftGrid a₀ Θ i * ((N i).card : ℝ) ≤ A * L ∧
      ¬ Lambda w T (shiftGrid a₀ Θ) (Finset.range I) ≤
        2 * boundedBandSum w N (shiftGrid a₀ Θ) I (bandCap A) / sigma0 + L / 100}
      ≤ ENNReal.ofReal (1 / 10000) := by sorry

end SublinearSteiner
