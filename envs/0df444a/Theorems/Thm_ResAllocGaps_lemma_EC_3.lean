-- Prove2me | Theorems.Thm_ResAllocGaps_lemma_EC_3
-- name    : ResAllocGaps.lemma_EC_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:28.565399+00:00
-- url     : https://prove2.me/theorems/c7318484-a8dc-4419-a1dc-48adcb8b821f
-- title:
--   Lemma EC.3 — $\mathbb P(\mathcal H_1),\mathbb P(\mathcal H_2),\mathbb P(\tilde{\mathcal H}_2)\ge p$ for large $T$ (corrected: some $p>0$ in place of $0.003$)
-- statement:
--   There are a constant $p>0$ and a horizon $T_0$ such that for every $\beta>0$ and every $T\ge T_0$, under the law $F_\beta$ with $B=\lfloor T/2\rfloor$,
--   $$\mathbb P(\mathcal H_1)\ge p,\qquad\mathbb P(\mathcal H_2)\ge p,\qquad\mathbb P(\tilde{\mathcal H}_2)\ge p .$$
--   The three events are deviations of order $\sqrt T$ of binomial counts of arrivals in $I_H$, whose success probability $\tfrac12-\tfrac{129}{256}T^{-1/2}$ does not depend on $\beta$.
--
--   Differences from the source:
--   - correction: P(H₁), P(H₂), P(H̃₂) ≥ 0.003 → ≥ p for some p > 0; reason: the printed bound fails for H₂: for any β > 0, F = F_β, B = ⌊T/2⌋, N(I_H, B+1, T) ∼ Bin(⌈T/2⌉, 1/2 − (129/256)T^{−1/2}) has mean ≥ T/4 − 0.26√T for T ≥ 32, so H₂ lies ≥ 2.74√T below it and Hoeffding gives P(H₂) < 10⁻¹² for every T ≥ 100; the proof of Theorem 1 needs only some positive constant
--   - generalization: β > 0 fixed, then T₀ → p and T₀ chosen before β, uniform over β > 0; reason: the laws of the three counts do not depend on β, so this specializes to each fixed β
-- source:
--   O. Besbes, Y. Kanoria and A. Kumar, Dynamic Resource Allocation: Algorithmic Design Principles and Spectrum of Achievable Performances, arXiv:2205.09078v2 (6 Oct 2023), https://arxiv.org/abs/2205.09078v2, Appendix EC.1, Lemma EC.3, p.ec6 (proof §EC.1.3, pp.ec9–ec10)

import Mathlib
import Definitions.Def_ResAllocGaps_OnlinePolicy
import Definitions.Def_ResAllocGaps_muBeta
import Definitions.Def_ResAllocGaps_arrivals

open MeasureTheory

namespace ResAllocGaps

/-- **Lemma EC.3** (corrected), Besbes, Kanoria & Kumar, arXiv:2205.09078v2, p.ec6: "There exists
`T₀ < ∞` such that for all `T ≥ T₀`, we have that `P(H₁), P(H₂), P(H̃₂) ≥ 0.003`", with the
constant `0.003` replaced by some `p > 0`, and `p`, `T₀` uniform over `β > 0`.

**Formalization Note (correction).** As printed the lemma is false for `H₂`: under `F_β` and
`B = ⌊T/2⌋`, `N(I_H, B + 1, T) ∼ Bin(⌈T/2⌉, 1/2 − (129/256)T^{−1/2})` has mean at least
`T/4 − 0.26√T` (`T ≥ 32`), so `H₂` lies at least `2.74√T` below it and Hoeffding's inequality gives
`P(H₂) < 10⁻¹²` for every `T ≥ 100`. The proof of Theorem 1 needs only some positive constant. The
laws of the three counts do not depend on `β` (the mass of `I_H` is `1/2 − (129/256)T^{−1/2}`). -/
theorem lemma_EC_3 :
    ∃ p : ℝ, 0 < p ∧ ∃ T₀ : ℕ, ∀ β : ℝ, 0 < β → ∀ T ≥ T₀,
      p ≤ ((sampleLaw (muBeta β) T) (eventH1 β T)).toReal ∧
      p ≤ ((sampleLaw (muBeta β) T) (eventH2 β T)).toReal ∧
      p ≤ ((sampleLaw (muBeta β) T) (eventH2t β T)).toReal := by sorry

end ResAllocGaps
