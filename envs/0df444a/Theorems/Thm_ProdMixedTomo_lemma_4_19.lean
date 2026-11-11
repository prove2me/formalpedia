-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_4_19
-- name    : ProdMixedTomo.lemma_4_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:55.740354+00:00
-- url     : https://prove2.me/theorems/a4087eb6-14e1-4a44-a541-09fcd2ef40db
-- title:
--   Lemma 4.19 — given (2) and (3), regularity (5) from $N\gtrsim n^2\log(n/\delta)/\epsilon^2$ samples
-- statement:
--   Let $T$ be $N$ i.i.d. samples from $\mathrm{Bern}(\mu)$, $\mu\in[0,1]^n$, $\epsilon,\delta>0$. For all constants $K_2,K_3$ there are constants $C,K_5$ such that if
--   $$
--   N\ \ge\ C\,\frac{n^2L(n/\delta)}{\epsilon^2},
--   $$
--   then the probability that Equations (2) (with $K_2$) and (3) (with $K_3$) hold but Equation (5) (with $K_5$) fails is at most $\delta/4$.
--
--   Differences from the source:
--   - reading: "Suppose … that Equations (2) and (3) hold. Then Equation (5) holds with probability 1 − δ/4" → Pr[(2) ∧ (3) ∧ ¬(5)] ≤ δ/4, for all constants K₂, K₃ of (2), (3) with C, K₅ depending on them; reason: the proof shows a VC event of probability 1 − δ/4 on which (2) and (3) imply (5) (readings R8, R9)
--   - reading: log(1/t) in an upper bound → max{1, log(1/t)} (logPlus), natural log; reason: the paper's convention, §2 Notation p.13
--   - encoding: "with probability 1 − δ/4" over i.i.d. samples T from π → the Bern(μ)^N mass of the sample lists on which the event fails, a finite sum; reason: the law of N i.i.d. samples on {0,1}^n
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.19, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_Weights
import Definitions.Def_ProdMixedTomo_Goodness

open Classical

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.19, p.32 (PDF p.34). Let `T` be `N` i.i.d. samples from `π = Bern(μ)`. If
`N ≳ n² log(n/δ)/ϵ²` and Equations (2) and (3) hold, then Equation (5) holds with probability
`1 − δ/4`.

**Formalization Note.** Read as: for all constants `K₂, K₃` of (2), (3) there are `C` and `K₅`
such that the `Bern(μ)^N`-mass of sample lists satisfying (2) and (3) but not (5) is at most `δ/4`.
Logs follow `log t ↦ max{1, log t}`. -/
theorem lemma_4_19 :
    ∀ K₂ K₃ : ℝ, ∃ C K₅ : ℝ, 0 < C ∧ 0 < K₅ ∧
    ∀ (n N : ℕ) (ϵ δ : ℝ) (μ : Fin n → ℝ), 0 < ϵ → 0 < δ → μ ∈ MeanBox n →
      C * (n : ℝ) ^ 2 * logPlus (n / δ) / ϵ ^ 2 ≤ N →
      ∑ T : Fin N → Cube n,
        (if Eq2 K₂ ϵ μ (pts T) ∧ Eq3 K₃ ϵ μ (pts T) ∧ ¬ Eq5 K₅ ϵ μ (pts T) then
          ∏ i, bern μ (T i) else 0) ≤ δ / 4 := by sorry

end ProdMixedTomo
