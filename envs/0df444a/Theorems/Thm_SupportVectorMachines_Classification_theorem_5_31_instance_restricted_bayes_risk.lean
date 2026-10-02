-- Prove2me | Theorems.Thm_SupportVectorMachines_Classification_theorem_5_31_instance_restricted_bayes_risk
-- name    : SupportVectorMachines.Classification.theorem_5_31_instance_restricted_bayes_risk
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:11:44.941222+00:00
-- url     : https://prove2.me/theorems/35ae0c73-8bef-406f-aee2-c71f0d5f95de
-- title:
--   Theorem 5.31 instance — the RKHS's restricted Bayes hinge risk equals the Bayes hinge risk
-- statement:
--   This is the hinge-loss instance of Theorem 5.31 (Approximation by p-integrable functions) of
--   Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 191), exactly as invoked
--   in the proof of Theorem 8.1 ("the hinge loss is also a $P$-integrable Nemitski loss of order
--   $1$ by Lemma 2.25, and hence Theorem 5.31 yields $R^*_{L,P,H} = R^*_{L,P}$").
--
--   Let $H$ be the RKHS of a measurable kernel $k$ over $X$ and $P$ a distribution on $X\times Y$
--   such that $H$ is dense in $L^1(P_X)$. Then $R^*_{L_{\mathrm{hinge}},P,H} = R^*_{L_{\mathrm{hinge}},P}$:
--   the smallest hinge risk attainable within $H$ equals the smallest hinge risk attainable by
--   *any* measurable function.
--
--   Theorem 5.31 itself is stated for a general continuous, $P$-integrable Nemitski loss of order
--   $p \in [1,\infty)$ and any dense $F \subset L^p(P_X)$; the hinge loss is such a loss for
--   $p = 1$ by Lemma 2.25 v) (every margin-based loss is a $P$-integrable Nemitski loss for every
--   $P$), so this specific instance ($L = L_{\mathrm{hinge}}$, $p=1$, $F=H$) is what Theorem 8.1's
--   proof actually needs.
--
--   **Formalization Note** The general Nemitski-loss apparatus (order $p$, growth bound) is not
--   restated: it is automatic for the hinge loss and not itself load-bearing for this instance,
--   per Hard Rule 9 ("restate the *specific instances* used"). `DenseInL1` is Definition
--   `RKHSAndSVM`'s $\varepsilon$-approximation rendering of denseness in $L^1(P_X)$.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 191, Theorem 5.31 (instantiated for the hinge loss as in the proof of Theorem 8.1, p. 289, citing Lemma 2.25 v))

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The hinge-loss instance of Theorem 5.31 (Approximation by p-integrable functions), p. 191,
used inside the proof of Theorem 8.1: since the hinge loss is a continuous, `P`-integrable
Nemitski loss of order `1` (Lemma 2.25 v)) and `H` is dense in `L¹(PX)`, the restricted Bayes
hinge risk on `H` coincides with the unrestricted Bayes hinge risk, `R*_{L_hinge,P,H} =
R*_{L_hinge,P}`. The general Nemitski-loss hypothesis is dropped: it is automatic for the hinge
loss by Lemma 2.25 v) and is not restated as machinery here, per Hard Rule 9. -/
theorem theorem_5_31_instance_restricted_bayes_risk {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hDense : DenseInL1 H toFun (P.map Prod.fst)) :
    restrictedBayesRisk H toFun hingeLoss P = bayesRisk hingeLoss P := by sorry

end SupportVectorMachines.Classification
