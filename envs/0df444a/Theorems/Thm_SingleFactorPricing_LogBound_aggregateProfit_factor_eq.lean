-- Prove2me | Theorems.Thm_SingleFactorPricing_LogBound_aggregateProfit_factor_eq
-- name    : SingleFactorPricing.LogBound.aggregateProfit_factor_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:57.899088+00:00
-- url     : https://prove2.me/theorems/9527b3ed-7d53-4af2-8a33-90728ffe73fc
-- title:
--   §2, p.4 — $R(qf)=qH(q)$
-- statement:
--   For every real $q$,
--
--   $$
--   R(qf)=q\,H(q).
--   $$
--
--   This links the profit along the direction $f$ to the demand appearing on the right side of A1.
--
--   Differences from the source:
--   - generalization: $q\ge0$ (the domain of $H$) → every real $q$, no hypothesis; reason: the identity is algebraic
--   - reading: $R(qf)=qf'd(qf)=qH(q)$ → only the outer identity $R(qf)=qH(q)$; reason: the middle term is $H(q)$ in vector notation, with $d$ the aggregate demand of p.5
--   - generalization: finitely many types $M$ with weights $\theta_j>0$, a positive $f$, non-negative demand → any measure $\mu$ on any type space, any $f$ and any demand; reason: the identity pulls the scalar $q$ out of a finite sum and an integral, which needs none of these; $T=$ `Fin m` with `KallMayerSLP.ICC.discreteLaw θ id` is the printed case
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_aggregateProfit
import Definitions.Def_SingleFactorPricing_LogBound_factorDemand

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **M4: `R(qf) = qH(q)`.** Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.4: "Finally, notice that
`R(qf) = qf′d(qf) = qH(q)`."

**Formalization Note.** The middle term is `H(q)` in vector notation, so only the outer identity is
stated. It needs no hypothesis and holds for every real `q`. -/
theorem aggregateProfit_factor_eq {N T : Type*} [Fintype N] [MeasurableSpace T] (μ : Measure T)
    (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ) (q : ℝ) :
    aggregateProfit μ d (q • f) = q * factorDemand μ d f q := by sorry

end SingleFactorPricing.LogBound
