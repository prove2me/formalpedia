-- Prove2me | Theorems.Thm_TalagrandConc_BinPacking_lemma_6_3
-- name    : TalagrandConc.BinPacking.lemma_6_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:24.46167+00:00
-- url     : https://prove2.me/theorems/f0b804b6-a51a-45da-b9c7-09072109e95b
-- title:
--   Lemma 6.3 — P(‖x‖₂ ≥ 2√N (E X₁²)^{1/2}) ≤ exp(−2N E X₁²)
-- statement:
--   Let $\mu$ be a probability measure on $[0,1]$ and $P = \mu^{\otimes N}$ the product probability on $[0,1]^N$, so that the coordinates $X_1,\dots,X_N$ are i.i.d. with law $\mu$. Write $\mathbb E X_1^2 = \int \omega^2\, d\mu(\omega)$ and $\|x\|_2 = (\sum_{i\le N} x_i^2)^{1/2}$. Then
--   $$P\big(\|x\|_2 \ge 2\sqrt N\,(\mathbb E X_1^2)^{1/2}\big) \le \exp(-2N\,\mathbb E X_1^2). \tag{6.3}$$
--
--   This tail bound disposes of the factor $\|x\|_2$ in (6.2).
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 152, Lemma 6.3, Eq. (6.3)

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.BinPacking

open MeasureTheory

/-- Talagrand (1995), p. 152, Lemma 6.3, Eq. (6.3): under the product probability
`P = μ^{⊗N}` on `[0,1]^N`, `P(‖x‖₂ ≥ 2 √N (E X₁²)^{1/2}) ≤ exp(−2 N E X₁²)`. -/
theorem lemma_6_3 (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ) :
    Measure.pi (fun _ : Fin N => μ)
        {x | 2 * Real.sqrt N * Real.sqrt (secondMoment μ) ≤ l2Norm x} ≤
      ENNReal.ofReal (Real.exp (-(2 * N * secondMoment μ))) := by sorry

end TalagrandConc.BinPacking
