-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_linearChange_indep_964b7f140ee7
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_linearChange_indep_964b7f140ee7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:59.220421+00:00
-- url     : https://prove2.me/theorems/5e5d5f2c-01ea-4a9f-bfd8-8035724c42da
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Lines Indep linear Change indep 964b7f140ee7: P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Lines Indep linear Change indep 964b7f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Lines Indep linear Change indep 964b7f140ee7 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Lines Indep linear Change indep 964b7f140ee7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeLinesIndep.lean#L23-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeLinesIndep.lean#L23-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeLinesIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeLinesIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_linearChange_indep_964b7f140ee7 {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] {N : ℕ}
    (P : Matrix (Fin N) (Fin N) Ω) (hP : IsUnit P) (t : Fin N → Φ) (ht : AlgebraicIndependent Ω t) :
    AlgebraicIndependent Ω (fun i => ∑ j, t j * algebraMap Ω Φ (P i j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairConeLinesIndep».«linearChange_indep» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_linearChange_indep_964b7f140ee7
