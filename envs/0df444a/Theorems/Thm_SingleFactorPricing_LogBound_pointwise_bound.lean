-- Prove2me | Theorems.Thm_SingleFactorPricing_LogBound_pointwise_bound
-- name    : SingleFactorPricing.LogBound.pointwise_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:45.255042+00:00
-- url     : https://prove2.me/theorems/e4bb6b9d-b134-461d-b34e-6d7a46361531
-- title:
--   Proof of Theorem 1, p.4 — $qG(q)\le\mathcal R^f$
-- statement:
--   Assume A1 and let $\mathcal R^f$ be the supremum of $R(qf)$ over $q>0$. Then, for every $q>0$,
--
--   $$
--   q\,G(q)\le\mathcal R^f .
--   $$
--
--   This combines the two steps in the paper: $qG(q)\le qH(q)=R(qf)$ by A1, and $R(qf)\le\mathcal R^f$.
--
--   Differences from the source:
--   - generalization: finitely many types $M$ with weights $\theta_j>0$, A0, a positive $f$, non-negative demand → any measure $\mu$ on any type space, any $\bar p$, any $f$ and any demand, with A1 the only hypothesis on them; reason: the step uses only A1, the identity $R(qf)=qH(q)$ and the definition of $\mathcal R^f$; $T=$ `Fin m` with `KallMayerSLP.ICC.discreteLaw θ id` is the printed case
--   - generalization: $\mathcal R^f$ a maximum → `IsLUB` of $R(qf)$ over $q>0$; reason: equal to the maximum when it exists
--   - reading: the chain $\int qG(q)\,dq/q\le\int R(qf)\,dq/q\le\mathcal R^f\int dq/q$ → the pointwise bound $qG(q)\le\mathcal R^f$, with $\int R(qf)\,dq/q$ not stated; reason: nothing makes $q\mapsto R(qf)$ measurable; the pointwise bound gives the printed conclusion directly
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, proof of Theorem 1, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_filteredDemand
import Definitions.Def_SingleFactorPricing_LogBound_AssumptionA1
import Definitions.Def_SingleFactorPricing_LogBound_IsSingleFactorOptimum

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **M5: the pointwise bound.** Gallego, Berbeglia, arXiv:2102.03038v2, proof of Theorem 1, p.4:
"the first inequality follows from `qG(q) ≤ qH(q) = R(qf)` due to A1. The second inequality follows
from `R(qf) ≤ Rᶠ`."

**Formalization Note.** The two steps are combined into `q G(q) ≤ Rᶠ` for `q > 0`. The line with
`∫ R(qf) dq/q` of the printed chain is not stated, because nothing makes `q ↦ R(qf)` measurable;
the proof of Theorem 1 needs only this pointwise bound. -/
theorem pointwise_bound {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (pbar : T → N → ℝ) (Rf : ℝ)
    (hA1 : AssumptionA1 μ d f pbar) (hRf : IsSingleFactorOptimum μ d f Rf) (q : ℝ) (hq : 0 < q) :
    q * filteredDemand μ d f pbar q ≤ Rf := by sorry

end SingleFactorPricing.LogBound
