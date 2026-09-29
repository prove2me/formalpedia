-- Prove2me | Theorems.Thm_Tensorization_klDiv_prod_eq_add
-- name    : Tensorization.klDiv_prod_eq_add
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T02:50:39.636935+00:00
-- url     : https://prove2.me/theorems/5e0d087a-a177-4221-bfa6-c7268dfe22be
-- title:
--   Tensorization of KL divergence over independent products
-- statement:
--   **Tensorization (sub-additivity) of Kullback–Leibler divergence over independent products.** For probability measures $\mu,\nu$ on $\alpha$ and $\pi,\rho$ on $\beta$, the relative entropy of the product measures splits additively: $$\mathrm{KL}(\mu\otimes\pi \,\|\, \nu\otimes\rho) = \mathrm{KL}(\mu\,\|\,\nu) + \mathrm{KL}(\pi\,\|\,\rho).$$ This is the tensorization identity at the heart of the entropy method (relative entropy of a product of independent coordinates is the sum of the per-coordinate relative entropies). It is proved from the Kullback–Leibler chain rule together with product commutativity. Boucheron–Lugosi–Massart, *Concentration Inequalities* (OUP 2013), Theorem 4.10 (sub-additivity / tensorization of entropy, derived from Han's inequality = the KL chain rule).

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

theorem Tensorization.klDiv_prod_eq_add {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ ν : Measure α) (π ρ : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure π] [IsProbabilityMeasure ρ] : klDiv (μ.prod π) (ν.prod ρ) = klDiv μ ν + klDiv π ρ := by sorry
