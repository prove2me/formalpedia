-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P82_transient_fluctuation_relations
-- name    : QAlgorithms.Papers.Independent.Intake100.P82.transient_fluctuation_relations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:09:40.638018+00:00
-- url     : https://prove2.me/theorems/b7e5d030-dbbe-4cb9-9428-564e77d5afce
-- title:
--   Proposition 1.1: transient fluctuation relations
-- statement:
--   For each positive integer $n$, let $(\Omega_n,\mathcal F_n,P_n)$ be an arbitrary probability space and let $\Theta_n$ be a measurable involution. Assume $\widehat P_n=(\Theta_n)_*P_n$ and $P_n$ are mutually absolutely continuous. Write $\sigma_n=\log(dP_n/d\widehat P_n)$ for a real almost-everywhere representative. No finite moment assumption is imposed.
--
--   Let $L_n$ be the law of $\sigma_n$ under $P_n$, let $\widehat L_n=(-\mathrm{id})_*L_n$, and put $e_n(\alpha)=\log\int e^{-\alpha\sigma_n}\,dP_n$, allowing $+\infty$. At every time,
--   $$e_n(\alpha)=e_n(1-\alpha)\quad(\alpha\in\mathbb R),\qquad L_n(ds)=e^s\widehat L_n(ds).$$
--   The scalar laws are equivalent and the Radon–Nikodym equality $dL_n/d\widehat L_n=e^s$ holds $\widehat L_n$-almost everywhere. This is the transient fluctuation relation, without a pointwise density assertion on null sets.
-- source:
--   Fluctuation Theorem and Thermodynamic Formalism, arXiv:1712.05167v3, PDF p. 12, Proposition 1.1: transient fluctuation relations

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P82

noncomputable section

open Filter MeasureTheory Set

open scoped Topology BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P82

attribute [local instance] Classical.propDecidable

/-- Proposition 1.1, arXiv:1712.05167v3, PDF p.12. Extended Laplace symmetry
and the density equality of the production law and its reflection. RN identity
is a.e.; equality as tilted measures also records equivalence of these laws. -/
theorem transient_fluctuation_relations {O : Type*} [MeasurableSpace O]
    (D : ReversalExperiment O) :
    (∀ a : ℝ, entropicFunctional D a = entropicFunctional D (1 - a)) ∧
    (let L := productionLaw D
     let Lhat := Measure.map (fun s : ℝ => -s) L
     L ≪ Lhat ∧ Lhat ≪ L ∧
     L = Lhat.withDensity (fun s => ENNReal.ofReal (Real.exp s)) ∧
     (∀ᵐ s ∂Lhat, L.rnDeriv Lhat s = ENNReal.ofReal (Real.exp s))) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P82

end
