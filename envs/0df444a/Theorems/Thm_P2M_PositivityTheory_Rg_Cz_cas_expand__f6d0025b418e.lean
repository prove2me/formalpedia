-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_cas_expand__f6d0025b418e
-- name    : P2M_PositivityTheory_Rg_Cz_cas_expand__f6d0025b418e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:19.742898+00:00
-- url     : https://prove2.me/theorems/d2948c36-4c3b-44d1-85ad-d75358245719
-- title:
--   P2 M Positivity Theory Rg Cz cas expand  f6d0025b418e: P2 M Positivity Theory Rg Cz cas expand  f6d0025b418e
-- statement:
--   The P2 M Positivity Theory Rg Cz cas expand  f6d0025b418e construction uses the P2 M Positivity Theory Rg Cz cas expand  f6d0025b418e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/Expand.lean#L66-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/Expand.lean#L66-L92

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_Expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

theorem P2M_PositivityTheory_Rg_Cz_cas_expand__f6d0025b418e (S : Finset Q) :
    (∑ a, ∑ c, tE S (0 : Fin n → Fin n → Module.End ℂ ℂ) a c * tE S 0 c a : Module.End ℂ (TV n ℂ Q)) =
      ((n * S.card : ℕ) : ℂ) • (1 : Module.End ℂ (TV n ℂ Q)) +
        ∑ p ∈ S, ∑ q ∈ S.erase p, pm (Equiv.swap p q) := by sorry

alias «PositivityTheory».«Rg».«Cz».«cas_expand'» := P2M_PositivityTheory_Rg_Cz_cas_expand__f6d0025b418e
