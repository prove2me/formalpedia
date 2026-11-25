-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_finiteDimensional_of_ringEquiv_c2d24250651f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_finiteDimensional_of_ringEquiv_c2d24250651f
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:48.693635+00:00
-- url     : https://prove2.me/theorems/ef385cdc-e7fc-43d7-9e6f-d23ccc6b379d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B finite Dimensional of ring Equiv c2d24250651f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B finit
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B finite Dimensional of ring Equiv c2d24250651f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B finite Dimensional of ring Equiv c2d24250651f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/NormLeOneIffIsIntegralElemOfEquiv.lean#L62-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_finiteDimensional_of_ringEquiv_c2d24250651f {E₁ E₂ L : Type*} [Field E₁] [Field E₂] [Field L]
    [Algebra E₁ L] [Algebra E₂ L] (e : E₂ ≃+* E₁)
    (he : algebraMap E₂ L = (algebraMap E₁ L).comp (e : E₂ →+* E₁)) [FiniteDimensional E₁ L] :
    FiniteDimensional E₂ L := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«finiteDimensional_of_ringEquiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_finiteDimensional_of_ringEquiv_c2d24250651f
