-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_genPar_algIndep_7c92d0181ec3
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_genPar_algIndep_7c92d0181ec3
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:46.874125+00:00
-- url     : https://prove2.me/theorems/702bca42-ae4b-4093-94dc-a26c515610dc
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Free Par Alg Indep gen Par alg Indep 7c92d0181ec3: P2 M Ground Theory Heights  Heights Vertical Free Par Alg Indep gen Par alg Indep 7c92d0181ec3
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Free Par Alg Indep gen Par alg Indep 7c92d0181ec3 construction uses the P2 M Ground Theory Heights  Heights Vertical Free Par Alg Indep gen Par alg Indep 7c92d0181ec3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFreeParAlgIndep.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFreeParAlgIndep.lean#L13-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFreeParAlgIndep
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
open GroundTheory.Heights₂.Heights.Vertical.FreeParAlgIndep

theorem P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_genPar_algIndep_7c92d0181ec3 (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«FreeParAlgIndep».«genPar_algIndep» := P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_genPar_algIndep_7c92d0181ec3
