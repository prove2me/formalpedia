-- Prove2me | Theorems.Thm_UpperTheory_V_Hi_iwMem
-- name    : UpperTheory.V.Hi.iwMem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:41:05.505723+00:00
-- url     : https://prove2.me/theorems/90efdf3e-beb6-4f73-8968-97c16d7288f7
-- title:
--   Hi: iw Mem
-- statement:
--   The Hi construction uses the iw Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/HeckeAlgebras/OrdinaryHeckeCharacters/IwMemMul.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/HeckeAlgebras/OrdinaryHeckeCharacters/IwMemMul.lean#L48-L62

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_OrdinaryHeckeCharacters_IwMemMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.iwMem :
    ∀ (G : Type) [Group G] (I : Iwa G) (c : ℕ) (g : G), (g ∈ I.Iw c ↔ ∃ x ∈ I.N, ∃ t ∈ I.T, ∃ y ∈ I.Nm c, g = x * t * y) ∧ (g ∈ I.I1 c ↔ ∃ x ∈ I.N, ∃ t ∈ I.Tc c, ∃ y ∈ I.Nm c, g = x * t * y) ∧ (g ∈ I.Nf → g ∈ I.Iw c → g ∈ I.N) := by sorry
