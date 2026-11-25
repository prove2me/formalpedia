-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_genPar_algIndep_175e337cdc44
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_genPar_algIndep_175e337cdc44
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:36.430848+00:00
-- url     : https://prove2.me/theorems/a9b53934-d0eb-4609-8357-bdcbe58333f1
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker gen Par alg Indep 175e337cdc44: P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker gen Par alg Indep 175e337cdc44
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker gen Par alg Indep 175e337cdc44 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Ker gen Par alg Indep 175e337cdc44 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecKer.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecKer.lean#L17-L27

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecKer

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_genPar_algIndep_175e337cdc44 (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecKer».«genPar_algIndep» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_genPar_algIndep_175e337cdc44
