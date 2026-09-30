-- Prove2me | Theorems.Thm_TierneyMH_Mixture_alphaMH_conditions
-- name    : TierneyMH.Mixture.alphaMH_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T02:45:27.344482+00:00
-- url     : https://prove2.me/theorems/d7a1b269-9d63-4a3b-9448-ed0b430bf427
-- title:
--   $\alpha_{MH}$ satisfies conditions (i) and (ii) of Theorem 2
-- statement:
--   Let $\pi$ be a probability measure and $Q$ a Markov proposal kernel on $E$, let $\mu(dx,dy)=\pi(dx)Q(x,dy)$, and let $R$, $r$ be the set and ratio of Proposition 1 constructed in its proof. Then the Metropolis–Hastings acceptance probability $\alpha_{MH}$ satisfies
--
--   1. (i) $\alpha_{MH}=0$ $\mu$-almost everywhere on $R^c$;
--   2. (ii) $\mu$-almost everywhere on $R$,
--
--   $$\alpha_{MH}(x,y)\,r(x,y)=\alpha_{MH}(y,x).$$
--
--   These are the two conditions of Theorem 2 of the paper, which together are necessary and sufficient for a Metropolis–Hastings kernel to satisfy detailed balance; so this result is what makes the kernel with acceptance probability $\alpha_{MH}$ reversible.
--
--   **Formalization Note** The page's display ends with "$=\alpha_{MH}(x,y)$"; condition (ii) and the computation require $\alpha_{MH}(y,x)$, since $\min\{r(x,y),1\}=\alpha_{MH}(y,x)$ on $R$. The statement uses the intended right-hand side. Conditions (i) and (ii) are restated here because Theorem 2 belongs to another mission of the series.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 3, §2 (α_MH satisfies conditions (i) and (ii) of Theorem 2)

import Mathlib
import Definitions.Def_TierneyMH_Mixture_canonR
import Definitions.Def_TierneyMH_Mixture_canonRatio
import Definitions.Def_TierneyMH_Mixture_alphaMH

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

/-- **`α_MH` satisfies conditions (i) and (ii) of Theorem 2** (Tierney 1998, §2, p. 3).
For `μ(dx, dy) = π(dx) Q(x, dy)` and the set `R = canonR π Q` and ratio `r = canonRatio π Q`
of Proposition 1:
* (i) `α_MH` is `μ`-almost everywhere zero on `Rᶜ`;
* (ii) `α_MH(x, y) r(x, y) = α_MH(y, x)` `μ`-almost everywhere on `R`.

(The page's display ends with "`= α_MH(x, y)`"; the right side required by (ii), and the
value of `min{r(x, y), 1}` on `R`, is `α_MH(y, x)`.) -/
theorem alphaMH_conditions {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q] :
    (∀ᵐ p ∂((π ⊗ₘ Q).restrict (canonR π Q)ᶜ), alphaMH π Q p = 0) ∧
      (∀ᵐ p ∂((π ⊗ₘ Q).restrict (canonR π Q)),
        alphaMH π Q p * canonRatio π Q p = alphaMH π Q p.swap) := by sorry

end TierneyMH.Mixture
