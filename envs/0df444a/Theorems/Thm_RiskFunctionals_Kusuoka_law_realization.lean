-- Prove2me | Theorems.Thm_RiskFunctionals_Kusuoka_law_realization
-- name    : RiskFunctionals.Kusuoka.law_realization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:35.489975+00:00
-- url     : https://prove2.me/theorems/8e628aa5-1347-4ac0-8bc1-7972939b3229
-- title:
--   Theorem A.2 — every law on a Polish space is realized on a non-atomic probability space
-- statement:
--   Let $X$ be a complete separable metric space with its Borel $\sigma$-algebra, and let $\mu$ be a probability measure on $X$. Let $(\Omega,\mathcal F,\mathbb P)$ be a non-atomic probability space (no measurable set of positive probability is an atom). Then there is an $\mathcal F$-measurable map $Y:\Omega\to X$ whose law is $\mu$:
--   $$\mathbb P\circ Y^{-1}=\mu .$$
--
--   This is the result that lets the proofs of the chapter assume without loss of generality that a version-independent functional lives on the standard space $[0,1]$ with Lebesgue measure, and that a prescribed joint distribution of a pair $(Y,Z)$ can be realized on the given space.
--
--   **Formalization Note** "Non-atomic" is the measure-theoretic notion of Appendix A (no atoms), not merely "singletons are null". The book's closing sentence ("In particular, the non-atomic probability space can be taken as $[0,1]$ with Lebesgue measure") is an instance of the statement and is not stated separately.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 266, Theorem A.2

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory ProbabilityTheory

namespace RiskFunctionals.Kusuoka

/-- Pflug & Römisch, p. 266, Theorem A.2: on a non-atomic probability space every Borel
probability measure on a complete separable metric space is the law of some random variable. -/
theorem law_realization {X : Type*} [MetricSpace X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsNonAtomic P) :
    ∃ Y : Ω → X, Measurable Y ∧ P.map Y = μ := by sorry

end RiskFunctionals.Kusuoka
