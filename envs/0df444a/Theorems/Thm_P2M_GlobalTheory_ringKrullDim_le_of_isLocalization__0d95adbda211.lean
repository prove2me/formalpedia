-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ringKrullDim_le_of_isLocalization__0d95adbda211
-- name    : P2M_GlobalTheory_ringKrullDim_le_of_isLocalization__0d95adbda211
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:34.370534+00:00
-- url     : https://prove2.me/theorems/2a1d6400-8e3b-48f2-8f3c-67b366a87c07
-- title:
--   P2 M Global Theory ring Krull Dim le of is Localization  0d95adbda211: P2 M Global Theory ring Krull Dim le of is Localization  0d95adbda211
-- statement:
--   The P2 M Global Theory ring Krull Dim le of is Localization  0d95adbda211 construction uses the P2 M Global Theory ring Krull Dim le of is Localization  0d95adbda211 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingKrullDimLtTopOfEssFiniteType.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingKrullDimLtTopOfEssFiniteType.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem P2M_GlobalTheory_ringKrullDim_le_of_isLocalization__0d95adbda211 {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by sorry

alias «GlobalTheory».«ringKrullDim_le_of_isLocalization'» := P2M_GlobalTheory_ringKrullDim_le_of_isLocalization__0d95adbda211
