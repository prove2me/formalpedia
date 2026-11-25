-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ConeImage_map_eval___93a91e452ef8
-- name    : P2M_GlobalTheory_ConeImage_map_eval___93a91e452ef8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:59.542469+00:00
-- url     : https://prove2.me/theorems/8b1c8cd7-d264-46a0-86fe-51a7a57bb2fe
-- title:
--   P2 M Global Theory Cone Image map eval   93a91e452ef8: P2 M Global Theory Cone Image map eval   93a91e452ef8
-- statement:
--   The P2 M Global Theory Cone Image map eval   93a91e452ef8 construction uses the P2 M Global Theory Cone Image map eval   93a91e452ef8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L119-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L119-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage

theorem P2M_GlobalTheory_ConeImage_map_eval___93a91e452ef8 {σ A : Type*} [CommRing A] [Algebra ℂ A] (j : MvPolynomial σ ℂ →ₐ[ℂ] A)
    (φ : A →ₐ[ℂ] ℂ) (a : A) (r : Polynomial (MvPolynomial σ ℂ)) :
    φ (r.eval₂ j.toRingHom a) =
      r.eval₂ (MvPolynomial.eval (fun i => φ (j (MvPolynomial.X i)))) (φ a) := by sorry

alias «GlobalTheory».«ConeImage».«map_eval₂'» := P2M_GlobalTheory_ConeImage_map_eval___93a91e452ef8
