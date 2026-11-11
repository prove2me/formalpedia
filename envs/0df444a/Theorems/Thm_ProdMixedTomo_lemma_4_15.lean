-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_4_15
-- name    : ProdMixedTomo.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:43.443202+00:00
-- url     : https://prove2.me/theorems/0f7ce39b-99a5-4ff5-96ce-3053afdd8d8f
-- title:
--   Lemma 4.15 — first-moment regularity (2) and (4) from $\tilde O((n\log(n/\epsilon)+\log(1/\delta))/\epsilon^2)$ samples
-- statement:
--   Let $T$ be $N$ i.i.d. samples from $\mathrm{Bern}(\mu)$, $\mu\in[0,1]^n$, $\epsilon,\delta>0$. There are universal constants $C,K$ such that if
--   $$
--   N\ \ge\ C\,\frac{n\,L(n/\epsilon)+L(1/\delta)}{\epsilon^2},
--   $$
--   then Equations (2) and (4) with constant $K$ hold simultaneously with probability at least $1-\delta/2$.
--
--   Differences from the source:
--   - encoding: O(·) / ≲ / Ω(·) → ∃ C > 0 chosen before n, N, ϵ, δ and μ; reason: meaning of a universal constant (p.13)
--   - reading: the ≲ inside Equations (2) and (4) → an explicit constant K, chosen with C; reason: Definition 4.11 puts ≲ in a definition (reading R8)
--   - reading: log(1/t) in an upper bound → max{1, log(1/t)} (logPlus), natural log; reason: the paper's convention, §2 Notation p.13
--   - encoding: "with probability 1 − δ/2" over i.i.d. samples T from π → the Bern(μ)^N mass of the sample lists on which the event fails, a finite sum; reason: the law of N i.i.d. samples on {0,1}^n
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.15, p.31 (PDF p.33); context §4.7, p.31

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_Weights
import Definitions.Def_ProdMixedTomo_Goodness

open Classical

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.15, p.31 (PDF p.33). Let `T` be `N` i.i.d. samples from `π = Bern(μ)`. If
`N ≳ (n log(n/ϵ) + log(1/δ))/ϵ²`, then Equations (2) and (4) hold simultaneously with probability
`1 − δ/2`.

**Formalization Note.** `≲` is an explicit universal `C`; the constant inside (2), (4) is an
explicit `K` (Definition 4.11 with `K`); logs follow the paper's convention `log t ↦ max{1, log t}`.
The failure probability is the `Bern(μ)^N`-mass of the sample lists for which (2) or (4) fails. -/
theorem lemma_4_15 :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (n N : ℕ) (ϵ δ : ℝ) (μ : Fin n → ℝ), 0 < ϵ → 0 < δ → μ ∈ MeanBox n →
      C * ((n : ℝ) * logPlus (n / ϵ) + logPlus (1 / δ)) / ϵ ^ 2 ≤ N →
      ∑ T : Fin N → Cube n,
        (if Eq2 K ϵ μ (pts T) ∧ Eq4 K ϵ μ (pts T) then 0 else ∏ i, bern μ (T i)) ≤ δ / 2 := by sorry

end ProdMixedTomo
