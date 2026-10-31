-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P93_assistance_regularization
-- name    : QAlgorithms.Papers.Independent.Intake100.P93.assistance_regularization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:37:46.5663+00:00
-- url     : https://prove2.me/theorems/a8705886-b828-47a0-90f3-28865928d3e2
-- title:
--   §III: assistance regularization is the operational rate
-- statement:
--   For a normalized mixed state $\rho^{AB}$ on two nonzero finite-dimensional spaces, let $E_A(\rho)$ be the maximum ensemble-average pure-state entanglement over decompositions of $\rho$. Let $E_A^\infty(\rho)$ be the operational i.i.d. Bell distillation yield with a purification held by the helper. The finite-ensemble maximum defining $E_A(\rho)$ is attained. The real limit exists and
--
--   $$\lim_{n\to\infty}\frac{E_A(\rho^{\otimes n})}{n}=E_A^\infty(\rho).$$
--
--   The sequence uses positive copy numbers, and entropies and rates are in bits. Pure states and zero-entropy marginals remain included. This identifies an independently defined operational rate with the regularized one-copy quantity.
-- source:
--   Entanglement of assistance and multipartite state distillation, arXiv:quant-ph/0505038v1, PDF p. 3, §III: assistance regularization is the operational rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P93

namespace QAlgorithms.Papers.Independent.Intake100.P93

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; no chunk-local aliases.

open Information100.P21 (Op)

open Information100.P08 (PureEnsemble)

open Dependency50.P07 (bipartiteProduct)

open Information100.P67 (receiverChannel)

open Support50.P11 (choiState)

/-- PDF p.3, Section III: regularization is a theorem, not the definition of
operational assistance; the positive-copy sequence has the stated real limit.
The one-copy supremum is attained, as required by the source's maximum. -/
theorem assistance_regularization {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (rho : Op (Fin a × Fin b)) (hrho : IsDensityMatrix rho) :
    (∃ ens : PureEnsemble (Fin a × Fin b), Information100.P08.pureAverage ens = rho ∧
      averageEntanglement ens = assistance rho) ∧
    Filter.Tendsto (assistanceSequence rho) Filter.atTop (nhds (operationalAssistance rho)) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P93
