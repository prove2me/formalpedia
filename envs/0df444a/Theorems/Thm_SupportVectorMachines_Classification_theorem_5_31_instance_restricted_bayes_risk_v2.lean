-- Prove2me | Theorems.Thm_SupportVectorMachines_Classification_theorem_5_31_instance_restricted_bayes_risk_v2
-- name    : SupportVectorMachines.Classification.theorem_5_31_instance_restricted_bayes_risk_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:25.185515+00:00
-- url     : https://prove2.me/theorems/694f0594-05c2-4a0d-8e88-314c27ed24b8
-- title:
--   Theorem 5.31 instance — the RKHS's restricted Bayes hinge risk equals the Bayes hinge risk ($[0,\infty]$-valued risks)
-- statement:
--   This is the hinge-loss instance of Theorem 5.31 (Approximation by $p$-integrable functions) of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 191), as invoked in the proof of Theorem 8.1 (p. 289): the hinge loss is a continuous $P$-integrable Nemitski loss of order $1$ by Lemma 2.25 v), hence Theorem 5.31 yields $R^*_{L,P,H} = R^*_{L,P}$.
--
--   Let $Y := \{-1,1\}$, $H$ be the RKHS of a measurable kernel $k$ over $X$, and $P$ a distribution on $X \times Y$ such that $H$ is dense in $L^1(P_X)$. Then
--   $$
--   R^*_{L_{\mathrm{hinge}},P,H} = R^*_{L_{\mathrm{hinge}},P},
--   $$
--   the smallest hinge risk attainable within $H$ equals the smallest hinge risk attainable by any measurable function (both in $[0,\infty]$).
--
--   **Formalization Note.** The retired version's risk was a real-valued Bochner integral, equal to the junk value $0$ for a measurable $f$ whose hinge integrand is not integrable, and its Bayes risk an unguarded real infimum over all measurable $f$; so $R^*_{L,P}$ collapsed to $0$ while every bounded $f \in H$ had risk $\ge 1$ (the accepted disproof). The corrected statement uses the $[0,\infty]$-valued Lebesgue risk of the bundled measurable nonnegative loss (Definition 2.1), with $R^*_{L,P}$ and $R^*_{L,P,H}$ infima in $[0,\infty]$, and adds the chapter's standing convention $Y = \{-1,1\}$ as $P(X \times \{-1,1\}) = 1$ (needed for Lemma 2.25 v): with unbounded real labels the hinge loss is not a Nemitski loss of order $1$). `IsRKHSOfKernel` includes the measurability of $k(\cdot,x)$ for every $x$ (Lemma 4.24), so every $f \in H$ is measurable; `DenseInL1` is the $\varepsilon$-approximation rendering of density in $L^1(P_X)$ by integrable elements of $H$. The general Nemitski apparatus is not restated (Hard Rule 9).
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 191, Theorem 5.31 (instantiated for the hinge loss as in the proof of Theorem 8.1, p. 289, citing Lemma 2.25 v))

import Mathlib
import Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2
import Definitions.Def_SupportVectorMachines_Classification_ClassificationLosses_v2
import Definitions.Def_SupportVectorMachines_Classification_RKHSAndSVM_v2

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- The hinge-loss instance of Theorem 5.31 (Approximation by p-integrable functions), Steinwart
& Christmann, *Support Vector Machines*, Springer 2008, p. 191, used inside the proof of Theorem
8.1 (p. 289): for `Y := {-1,1}` (binary classification; `P` is supported on `X × {-1,1}`), the
hinge loss is a continuous, `P`-integrable Nemitski loss of order `1` (Lemma 2.25 v)), so if `H`
is the RKHS of a measurable kernel over `X` and `H` is dense in `L¹(PX)`, the restricted Bayes
hinge risk on `H` coincides with the unrestricted Bayes hinge risk,
`R*_{L_hinge,P,H} = R*_{L_hinge,P}` (both in `[0,∞]`). The general Nemitski-loss hypothesis is
dropped: it is automatic for the hinge loss by Lemma 2.25 v) and is not restated as machinery
here, per Hard Rule 9.
Corrected version of `theorem_5_31_instance_restricted_bayes_risk`, whose risks were real-valued
Bochner integrals (junk `0` for a non-integrable hinge integrand, collapsing the Bayes risk) and
which allowed arbitrary real labels. -/
theorem theorem_5_31_instance_restricted_bayes_risk_v2 {X : Type*} [MeasurableSpace X]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) (hRKHS : IsRKHSOfKernel H toFun k)
    (P : Measure (X × ℝ)) [IsProbabilityMeasure P]
    (hY : P (Set.univ ×ˢ ({-1, 1} : Set ℝ)) = 1)
    (hDense : DenseInL1 H toFun (P.map Prod.fst)) :
    restrictedBayesRisk H toFun hingeLoss P = bayesRisk hingeLoss P := by sorry

end SupportVectorMachines.Classification
