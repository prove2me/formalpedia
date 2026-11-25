-- Prove2me | Theorems.Thm_P2M_Formalism_BasicNotions_Examples__NZ_not_le_of_prod_10e9f6327452
-- name    : P2M_Formalism_BasicNotions_Examples__NZ_not_le_of_prod_10e9f6327452
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:19.348859+00:00
-- url     : https://prove2.me/theorems/07ad19fe-4aad-4551-ac1e-36f8375d8523
-- title:
--   P2 M Formalism Basic Notions Examples  NZ not le of prod 10e9f6327452: P2 M Formalism Basic Notions Examples  NZ not le of prod 10e9f6327452
-- statement:
--   The P2 M Formalism Basic Notions Examples  NZ not le of prod 10e9f6327452 construction uses the P2 M Formalism Basic Notions Examples  NZ not le of prod 10e9f6327452 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZColB.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NZColB.lean#L11-L17

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NZColB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.NZ
open IsDedekindDomain
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]

theorem P2M_Formalism_BasicNotions_Examples__NZ_not_le_of_prod_10e9f6327452 {S : Finset (HeightOneSpectrum R)} (m : HeightOneSpectrum R → ℕ) (w : HeightOneSpectrum R)
    (hw : w ∉ S) : ¬ (∏ v ∈ S, v.asIdeal ^ m v) ≤ w.asIdeal := by sorry

alias «Formalism».«BasicNotions».«Examples₂».«NZ».«not_le_of_prod» := P2M_Formalism_BasicNotions_Examples__NZ_not_le_of_prod_10e9f6327452
