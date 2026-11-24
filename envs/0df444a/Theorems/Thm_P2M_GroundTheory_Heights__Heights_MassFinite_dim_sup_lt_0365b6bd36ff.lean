-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MassFinite_dim_sup_lt_0365b6bd36ff
-- name    : P2M_GroundTheory_Heights__Heights_MassFinite_dim_sup_lt_0365b6bd36ff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:48.061827+00:00
-- url     : https://prove2.me/theorems/e28b7b94-67d9-4dd5-bb62-43f49363984a
-- title:
--   P2 M Ground Theory Heights  Heights Mass Finite dim sup lt 0365b6bd36ff: P2 M Ground Theory Heights  Heights Mass Finite dim sup lt 0365b6bd36ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Mass Finite dim sup lt 0365b6bd36ff construction uses the P2 M Ground Theory Heights  Heights Mass Finite dim sup lt 0365b6bd36ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L44-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFinite.lean#L44-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.MassFinite

theorem P2M_GroundTheory_Heights__Heights_MassFinite_dim_sup_lt_0365b6bd36ff {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (f : MvPolynomial (Fin n) ℂ) (hf : f ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) < d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MassFinite».«dim_sup_lt» := P2M_GroundTheory_Heights__Heights_MassFinite_dim_sup_lt_0365b6bd36ff
