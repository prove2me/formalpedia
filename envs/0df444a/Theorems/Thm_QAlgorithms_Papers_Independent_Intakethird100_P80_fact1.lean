-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_fact1
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.fact1
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T09:21:55.226277+00:00
-- url     : https://prove2.me/theorems/a0ede062-2740-4142-ba17-d841bcd57a32
-- title:
--   Ordering and positivity of statistical strengths
-- statement:
--   Fix a finite quantum experiment $Q$, with nonempty setting and outcome alphabets. A local theory is any probability law on all potential outcomes; its predictions are coordinate marginals. Let $U(\sigma,\pi)=D_2(Q_\sigma\|P_{\sigma;\pi})$, with the same setting law on both sides. Define $u(\sigma)=\inf_\pi U(\sigma,\pi)$, $S^{\rm UNI}=u(\sigma^\circ)$ for uniform settings, $S^{\rm UC}=\sup_{\sigma\text{ product}}u(\sigma)$, and $S^{\rm COR}=\sup_\sigma u(\sigma)$. Then
--
--   $$S^{\rm UNI}\le S^{\rm UC}\le S^{\rm COR},\qquad S^{\rm UNI}>0\ \Longleftrightarrow\ Q\text{ has no local model}.$$
--
--   This relates the three experimental freedoms and detects proper nonlocality. All divergences are in bits and may initially take the value $+\infty$.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 8, Fact 1: ordering and positivity of statistical strengths

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF p.8, Fact 1: ordering and strict positivity of the UNIFORM strength. -/
theorem fact1 {S : BellExperiment} (Q : Table S) (hQ : NonlocalityProof Q) :
    uniformStrength Q ≤ uncorrelatedStrength Q ∧
    uncorrelatedStrength Q ≤ correlatedStrength Q ∧
    (0 < uniformStrength Q ↔ Proper Q) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
