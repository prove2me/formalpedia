-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_X_59eac33e54da
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_X_59eac33e54da
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:08:27.097114+00:00
-- url     : https://prove2.me/theorems/3c17af66-a5fc-4726-9c5b-ad5673f3b627
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous prod map X 59eac33e54da: P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous prod ma
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous prod map X 59eac33e54da construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous prod map X 59eac33e54da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L43-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSymmetricSpanHsymm
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
open MvPolynomial Finset
open GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
omit [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_X_59eac33e54da (t : Multiset σ) :
    ((t.map (X : σ → MvPolynomial σ ℤ)).prod).IsHomogeneous (Multiset.card t) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SymmetricSpanHsymm».«isHomogeneous_prod_map_X» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_X_59eac33e54da
