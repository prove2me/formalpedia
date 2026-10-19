-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_conditionalTOUpgrade
-- name    : QAlgorithms.Papers.Independent.Information100.P44.conditionalTOUpgrade
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:40:06.150977+00:00
-- url     : https://prove2.me/theorems/3688bd33-cdc3-4e8a-9d84-e38930a06c5e
-- title:
--   Proposition 2: conditional upgrade to TO-sharp certificate
-- statement:
--   In the fixed four-level instance, let $L_k^{\star,\rm CGP}$ be the finite CGP optima. Let $L_k^{\star,\rm TO}$ and $S_{\rm sum}^{\star,\rm TO}$ be the individual and summed suprema over finite-bath thermal operations with the required coarse target populations, using extended-real suprema so an empty set has supremum $-\infty$. Assume the presently unproved bridge $L_k^{\star,\rm TO}=L_k^{\star,\rm CGP}$ for all three objectives. Then
--   $$S_{\rm sum}^{\star,\rm TO}<\sum_kL_k^{\star,\rm TO}.$$
--   No feasible finite thermal operation jointly attains its three individual TO optima. The bridge is an explicit antecedent; no thermal feasibility or closure attainment is silently assumed.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 19, Proposition 2: conditional upgrade to TO-sharp certificate

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.19, Proposition 2: explicitly conditional on the unproved equality bridge;
extended-real TO suprema prevent a junk optimum for an empty feasible set. -/
theorem conditionalTOUpgrade
    (hbridge : ∀ k : Fin 3, toOptimum k = (cgpOptimum k : EReal)) :
    toSumOptimum < ∑ k : Fin 3, toOptimum k ∧
    ¬ ∃ Phi : Map 4, FixedTOFeasible Phi ∧
      ∀ k : Fin 3, (channelObjective k Phi : EReal) = toOptimum k := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
