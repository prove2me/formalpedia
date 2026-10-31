-- Prove2me | Theorems.Thm_QiFixedDesign_Concentration_lemma_8
-- name    : QiFixedDesign.Concentration.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:59:17.478644+00:00
-- url     : https://prove2.me/theorems/553c3cfb-6a0e-4205-93ed-770584008ff4
-- title:
--   Lemma 8 — translation distance for arbitrary real probability laws
-- statement:
--   Let $\mu,\nu$ be arbitrary Borel probability measures on $\mathbb R$. If for some real $t$, $\nu$ is the law of $u+t$ when $u$ has law $\mu$, then
--   $$W_1(\mu,\nu)=|t|.$$
--   No first-moment, density or finite-support assumption is imposed. Thus the statement includes atomic laws and heavy-tailed laws. The printed density-based proof has a gap for atoms, but this is not a restriction of the target.
--
--   Differences from the source:
--   - encoding: probabilities and possibly infinite transport costs → nonnegative extended real measures and coupling costs; reason: infinite costs stay infinite and finite probabilities have their usual values
--   - encoding: d nu(x+t)=d mu(x) → nu is the pushforward of mu under translation by t; reason: translation of measures makes sense for all probability laws, including atoms
-- source:
--   Qi, Cao and Shen (2021), Distributionally Robust Conditional Quantile Prediction with Fixed Design, DOI 10.1287/mnsc.2020.3903, supplied source.pdf, Lemma 8, PDF/printed p. 19; proof pp. 19–20

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace QiFixedDesign.Concentration

theorem lemma_8 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t : ℝ) (hν : ν = μ.map (fun u => u + t)) :
    WassersteinDRO.Duality.wassersteinDistance 1 μ ν = ENNReal.ofReal |t| := by sorry

end QiFixedDesign.Concentration
