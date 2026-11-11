-- Prove2me | Theorems.Thm_ProdMixedTomo_lemma_4_12
-- name    : ProdMixedTomo.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:27.807203+00:00
-- url     : https://prove2.me/theorems/40d4413a-0953-4ea6-b579-8946259fd671
-- title:
--   Lemma 4.12 — $\tilde O(n^2/\epsilon^2)$ samples are $\epsilon$-good with probability $0.99$
-- statement:
--   There are universal constants $C,K$ such that for every $\epsilon>0$ and $\mu\in[0,1]^n$, if $T$ is a list of
--   $$
--   N\ \ge\ C\cdot X\cdot(\log(2+X))^C,\qquad X=n^2/\epsilon^2,
--   $$
--   independent samples from $\mathrm{Bern}(\mu)$, then with probability at least $0.99$ the list $T$ is $(K,\epsilon)$-good for $\mathrm{Bern}(\mu)$. It is the statistical input of the filter: the clean samples satisfy the deterministic regularity conditions.
--
--   Differences from the source:
--   - reading: N₀ = Õ(n²/ϵ²) → C·X·(log(2 + X))^C with X = n²/ϵ²; reason: polylog of the printed argument (reading R2)
--   - reading: "ϵ-good" (Definition 4.11 with ≲) → (K, ϵ)-good with an explicit K chosen with C, before all data; reason: reading R8
--   - encoding: "with probability 0.99" over i.i.d. samples T from π → the Bern(μ)^N mass of the sample lists on which the event fails, a finite sum; reason: the law of N i.i.d. samples on {0,1}^n
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.12, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates
import Definitions.Def_ProdMixedTomo_BinaryProduct
import Definitions.Def_ProdMixedTomo_Weights
import Definitions.Def_ProdMixedTomo_Goodness

open Classical

namespace ProdMixedTomo

/-- Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), Lemma 4.12, p.26 (PDF p.28). Let `ϵ > 0` and let `T` be `N ≥ N₀ = Õ(n²/ϵ²)` independent samples
from `π = Bern(μ)`. Then with probability `0.99`, `T` is an `ϵ`-good set of points for `π`.

**Formalization Note.** `Õ(X) = C·X·(log(2 + X))^C`; goodness is `(K, ϵ)`-goodness with an
explicit `K` chosen with `C`, before all data. -/
theorem lemma_4_12 :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (n N : ℕ) (ϵ : ℝ) (μ : Fin n → ℝ), 0 < ϵ → μ ∈ MeanBox n →
      otilde C ((n : ℝ) ^ 2 / ϵ ^ 2) ≤ N →
      ∑ T : Fin N → Cube n, (if IsGood K ϵ μ (pts T) then 0 else ∏ i, bern μ (T i)) ≤
        1 / 100 := by sorry

end ProdMixedTomo
