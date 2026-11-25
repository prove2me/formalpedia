-- Prove2me | Theorems.Thm_P2M_Formalism_HC_Frame_hostOrbits__2cb81a5b86d8
-- name    : P2M_Formalism_HC_Frame_hostOrbits__2cb81a5b86d8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:56:30.138616+00:00
-- url     : https://prove2.me/theorems/ec452077-ae66-494b-9e58-3c4fd945e641
-- title:
--   P2 M Formalism HC Frame host Orbits  2cb81a5b86d8: P2 M Formalism HC Frame host Orbits  2cb81a5b86d8
-- statement:
--   The P2 M Formalism HC Frame host Orbits  2cb81a5b86d8 construction uses the P2 M Formalism HC Frame host Orbits  2cb81a5b86d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L603-L609
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/FrameFacts.lean#L603-L609

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)

theorem P2M_Formalism_HC_Frame_hostOrbits__2cb81a5b86d8 (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) :
    (∀ τ ∈ φ.Psi, ∀ i : ℕ, g ^ i * τ ∈ φ.Psi ↔ Even i) ∧
    (g.1 = c0 → Even (orderOf g.2) → orderOf g = orderOf g.2) := by sorry

alias «Formalism».«HC».«Frame».«hostOrbits'» := P2M_Formalism_HC_Frame_hostOrbits__2cb81a5b86d8
