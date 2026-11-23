-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__emptyPlaces_natAct_93c637f18902
-- name    : P2M_Formalism_BasicNotions_Examples__emptyPlaces_natAct_93c637f18902
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:34.803323+00:00
-- url     : https://prove2.me/theorems/5ac85868-6d7f-4700-8e4d-fee256b03f8a
-- title:
--   P2 M Formalism Basic Notions Examples  empty Places nat Act 93c637f18902: P2 M Formalism Basic Notions Examples  empty Places nat Act 93c637f18902
-- statement:
--   The P2 M Formalism Basic Notions Examples  empty Places nat Act 93c637f18902 construction uses the P2 M Formalism Basic Notions Examples  empty Places nat Act 93c637f18902 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean#L134-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/GPlacesExampleNatAct.lean#L134-L143

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GPlacesExampleNatAct
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
open Formalism.BasicNotions NumberField IsDedekindDomain
open Formalism.MainNotions.G

theorem P2M_Formalism_BasicNotions_Examples__emptyPlaces_natAct_93c637f18902 (p : ℕ) (A : ∀ v, GL (Fin ((emptyPlaces p).m + 1)) ((emptyPlaces p).Qq v)) :
    (emptyPlaces p).natAct A = LinearMap.id := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«emptyPlaces_natAct» := P2M_Formalism_BasicNotions_Examples__emptyPlaces_natAct_93c637f18902
