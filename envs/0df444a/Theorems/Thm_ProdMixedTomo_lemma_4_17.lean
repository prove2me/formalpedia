-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_4_17
-- name    : ProdMixedTomo.lemma_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:43.172907+00:00
-- url     : https://prove2.me/theorems/5ea7b99d-43eb-49d9-bc53-681849013850
-- title:
--   Lemma 4.17 — second-moment regularity (3) from $N\gtrsim n^2/\epsilon^2$ samples
-- statement:
--   Let $T$ be $N$ i.i.d. samples from $\mathrm{Bern}(\mu)$, $\mu\in[0,1]^n$, $\epsilon>0$. There are universal constants $C,K$ such that if $N\ge Cn^2/\epsilon^2$, then Equation (3) with constant $K$ (for every $\mu'\in[0,1]^n$ with $\mu'\ge\mu/3$) holds with probability at least $0.99$.
--
--   Differences from the source:
--   - encoding: O(·) / ≲ / Ω(·) → ∃ C > 0 chosen before n, N, ϵ and μ; reason: meaning of a universal constant (p.13)
--   - reading: the ≲ inside Equation (3) → an explicit constant K, chosen with C; reason: reading R8
--   - encoding: "with probability ≥ 0.99" over i.i.d. samples T from π → the Bern(μ)^N mass of the sample lists on which the event fails, a finite sum; reason: the law of N i.i.d. samples on {0,1}^n
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.17, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_Weights
import Definitions.Def_ProdMixedTomo_Goodness

open Classical

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.17, p.32 (PDF p.34). Let `T` be `N` i.i.d. samples from `π = Bern(μ)`. If
`N ≳ n²/ϵ²`, then Equation (3) holds with probability `≥ 0.99`.

**Formalization Note.** `≲` is an explicit universal `C`; (3) carries an explicit constant `K` and
quantifies over every `μ' ∈ [0,1]ⁿ` with `μ' ≥ μ/3`. -/
theorem lemma_4_17 :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (n N : ℕ) (ϵ : ℝ) (μ : Fin n → ℝ), 0 < ϵ → μ ∈ MeanBox n →
      C * (n : ℝ) ^ 2 / ϵ ^ 2 ≤ N →
      ∑ T : Fin N → Cube n, (if Eq3 K ϵ μ (pts T) then 0 else ∏ i, bern μ (T i)) ≤ 1 / 100 := by sorry

end ProdMixedTomo
