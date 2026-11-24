-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__diag_congr_3bcbdc2a3fa9
-- name    : P2M_Formalism_BasicNotions_Examples__diag_congr_3bcbdc2a3fa9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:27:33.409345+00:00
-- url     : https://prove2.me/theorems/7582f5d4-e13a-40a0-a0b2-4987c3cb9439
-- title:
--   P2 M Formalism Basic Notions Examples  diag congr 3bcbdc2a3fa9: P2 M Formalism Basic Notions Examples  diag congr 3bcbdc2a3fa9
-- statement:
--   The P2 M Formalism Basic Notions Examples  diag congr 3bcbdc2a3fa9 construction uses the P2 M Formalism Basic Notions Examples  diag congr 3bcbdc2a3fa9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean#L328-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Spaces.lean#L328-L334

import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Definitions.Def_Formalism_FockGram_SymGramPosSemidef
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
open NumberField
open scoped TensorProduct
open IsDedekindDomain

theorem P2M_Formalism_BasicNotions_Examples__diag_congr_3bcbdc2a3fa9 {n A : Type} [Fintype n] [DecidableEq n] [CommRing A] (σ : A →+* A)
    (d s t : n → A) (h : ∀ i, σ (d i) * s i * d i = t i) :
    Formalism.UG.cT σ (Matrix.diagonal d) * Matrix.diagonal s * Matrix.diagonal d = Matrix.diagonal t := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«diag_congr» := P2M_Formalism_BasicNotions_Examples__diag_congr_3bcbdc2a3fa9
