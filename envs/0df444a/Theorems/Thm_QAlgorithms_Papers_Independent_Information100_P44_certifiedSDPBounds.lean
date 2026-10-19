-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_certifiedSDPBounds
-- name    : QAlgorithms.Papers.Independent.Information100.P44.certifiedSDPBounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:39:31.47249+00:00
-- url     : https://prove2.me/theorems/d2a50139-34aa-45b9-8acb-19355ea1488c
-- title:
--   Lemma 4: certified SDP bounds
-- statement:
--   For the fixed four-level CGP instance of Eqs. (110)–(121), write $L_k^\star$ for the supremum of signed objective $k\in\{01a,1b3,03\}$, and $S_{\rm sum}^\star$ for the supremum of their sum over one common feasible channel. The certified rational bounds are
--   $$\sum_kL_k^\star\ge0.1030097>0.1030090,\qquad S_{\rm sum}^\star\le0.0881264<0.0881270.$$
--   Every terminating decimal denotes its exact rational value. Witness feasibility and numerical certificates are conclusions used to justify these bounds, not hypotheses. This is the certified separation, not an assertion that floating solver estimates are exact.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 18, Lemma 4: certified SDP bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.18, Lemma 4, Eqs.(132)–(133): exact rational certified bounds, with no witness assumptions. -/
theorem certifiedSDPBounds :
    (1030097/10000000 : ℝ) ≤ (∑ k : Fin 3, cgpOptimum k) ∧
    (1030090/10000000 : ℝ) < 1030097/10000000 ∧
    cgpSumOptimum ≤ (881264/10000000 : ℝ) ∧
    (881264/10000000 : ℝ) < 881270/10000000 := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
