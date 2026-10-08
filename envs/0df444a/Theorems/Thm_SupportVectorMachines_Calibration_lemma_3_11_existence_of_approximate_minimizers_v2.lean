-- Prove2me | Theorems.Thm_SupportVectorMachines_Calibration_lemma_3_11_existence_of_approximate_minimizers_v2
-- name    : SupportVectorMachines.Calibration.lemma_3_11_existence_of_approximate_minimizers_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:43:04.722031+00:00
-- url     : https://prove2.me/theorems/e3189f21-5291-4ec7-820a-308b1c046788
-- title:
--   Lemma 3.11 — finiteness of the minimal inner risk characterizes existence of approximate minimizers (measurable loss)
-- statement:
--   This is Lemma 3.11 (Existence of approximate minimizers) of Steinwart & Christmann, *Support Vector Machines* (Springer 2008, p. 57), cited in the proof of Theorem 3.17.
--
--   Let $X$ be a complete measurable space, $L$ a loss (Definition 2.1: measurable and nonnegative), $P$ a distribution on $X \times Y$ represented by $(P_X,\kappa)$, and $\varepsilon \in (0,\infty]$. Then the following are equivalent:
--
--   1. $C^*_{L,P(\cdot\mid x),x} < \infty$ for $P_X$-almost all $x \in X$;
--   2. there exists a measurable $f : X \to \mathbb R$ with $f(x) \in M_{L,P(\cdot\mid x),x}(\varepsilon)$ for $P_X$-almost all $x \in X$.
--
--   **Formalization Note.** The retired version quantified over the bare function type for $L$; a loss whose unique $\varepsilon$-minimizer depends non-measurably on $x$ admits no measurable selection, which refuted (i) ⇒ (ii). The corrected statement takes $L$ in the bundled `Loss X` (measurable and nonnegative), as Definition 2.1 and the measurable-selection step of the proof require, and uses the book's definition of a complete measurable space. $\varepsilon$ ranges over `ENNReal` with $0 < \varepsilon$, i.e. over $(0,\infty]$ exactly. Conventions made explicit (common to the corrected Chapter 3 milestones): a loss is the bundled `Loss X` of Definition 2.1 — measurable on $X \times \mathbb R \times \mathbb R$ and nonnegative — with the closed label set $Y$ embedded in $\mathbb R$ (a loss on $X \times Y \times \mathbb R$ extends by $0$ outside $Y$, a distribution on $X \times Y$ is one on $X \times \mathbb R$ supported on $X \times Y$, and a set $\mathcal Q$ of distributions on $Y$ is a set of measures on $\mathbb R$); a distribution $P$ on $X \times Y$ is represented by its marginal $P_X$ (a probability measure) together with a measurable family $\kappa : X \to \mathcal M(\mathbb R)$ of probability measures, the regular conditional probabilities $P(\cdot\mid x)$ (which exist since $Y$ is Polish, Lemma A.3.16; every statement is invariant under the choice of version), so that risks are written in the form of Eq. (3.5); all risks are $[0,\infty]$-valued Lebesgue integrals, as in the book; and `IsCompleteMeasurableSpace` is now the book's own notion (the $\sigma$-algebra equals its universal completion) instead of the retired stronger sufficient condition.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 57, Lemma 3.11

import Mathlib
import Definitions.Def_SupportVectorMachines_Calibration_Loss_v2
import Definitions.Def_SupportVectorMachines_Calibration_InnerRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_OuterRisks_v2
import Definitions.Def_SupportVectorMachines_Calibration_IsCompleteMeasurableSpace_v2

open MeasureTheory

namespace SupportVectorMachines.Calibration

/-- Lemma 3.11 (Existence of approximate minimizers), Steinwart & Christmann, *Support Vector
Machines*, Springer 2008, p. 57: let `X` be a complete measurable space,
`L : X × Y × ℝ → [0,∞)` be a loss (Definition 2.1: measurable and nonnegative, bundled in
`Loss X`), `P` (represented by `(PX, κ)`, `κ` a measurable family of conditional distributions
`P(·|x)`) be a distribution on `X × ℝ`, and `ε ∈ (0,∞]`. Then the following are equivalent:
i) `C*_{L,P(·|x),x} < ∞` for `PX`-almost all `x ∈ X`; ii) there exists a measurable `f : X → ℝ`
such that `f(x) ∈ M_{L,P(·|x),x}(ε)` for `PX`-almost all `x ∈ X`.
Corrected version of `lemma_3_11_existence_of_approximate_minimizers`, whose `Loss X` was the
bare function type (no measurability, so no measurable selection existed), and whose
completeness notion was a stronger sufficient condition. -/
theorem lemma_3_11_existence_of_approximate_minimizers_v2 {X : Type*} [MeasurableSpace X]
    (hX : IsCompleteMeasurableSpace X) (L : Loss X)
    (PX : Measure X) [IsProbabilityMeasure PX] (κ : X → Measure ℝ) (hκ : Measurable κ)
    (hκprob : ∀ x, IsProbabilityMeasure (κ x))
    (ε : ENNReal) (hε : 0 < ε) :
    (∀ᵐ x ∂PX, minInnerRisk L (κ x) x < ⊤) ↔
      ∃ f : X → ℝ, Measurable f ∧ ∀ᵐ x ∂PX, f x ∈ approxMinimizers L (κ x) x ε := by sorry

end SupportVectorMachines.Calibration
