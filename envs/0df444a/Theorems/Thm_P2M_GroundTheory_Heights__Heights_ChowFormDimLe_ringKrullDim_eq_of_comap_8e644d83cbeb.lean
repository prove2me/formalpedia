-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowFormDimLe_ringKrullDim_eq_of_comap_8e644d83cbeb
-- name    : P2M_GroundTheory_Heights__Heights_ChowFormDimLe_ringKrullDim_eq_of_comap_8e644d83cbeb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:38:23.246138+00:00
-- url     : https://prove2.me/theorems/fd7a24c3-1873-4a57-bb93-c375160076f2
-- title:
--   P2 M Ground Theory Heights  Heights Chow Form Dim Le ring Krull Dim eq of comap 8e644d83cbeb: P2 M Ground Theory Heights  Heights Chow Form Dim Le ring Krull Dim eq of comap 8e644d83cbeb
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Form Dim Le ring Krull Dim eq of comap 8e644d83cbeb construction uses the P2 M Ground Theory Heights  Heights Chow Form Dim Le ring Krull Dim eq of comap 8e644d83cbeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormDimLe.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormDimLe.lean#L42-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChowFormDim
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormDimLe
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChowFormDimLe

theorem P2M_GroundTheory_Heights__Heights_ChowFormDimLe_ringKrullDim_eq_of_comap_8e644d83cbeb {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F))
    (P : Ideal (MvPolynomial (Fin n) K)) (hPI : P.comap (MvPolynomial.map (algebraMap F K)) = I) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowFormDimLe».«ringKrullDim_eq_of_comap» := P2M_GroundTheory_Heights__Heights_ChowFormDimLe_ringKrullDim_eq_of_comap_8e644d83cbeb
