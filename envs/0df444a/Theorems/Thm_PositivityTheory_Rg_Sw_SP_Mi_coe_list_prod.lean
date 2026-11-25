-- Prove2me | Theorems.Thm_PositivityTheory_Rg_Sw_SP_Mi_coe_list_prod
-- name    : PositivityTheory.Rg.Sw.SP.Mi.coe_list_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:59:36.189943+00:00
-- url     : https://prove2.me/theorems/5e4d29e9-f310-5f5f-a7dd-1fc944dc9565
-- title:
--   Mi: coe list prod
-- statement:
--   The Mi construction uses the coe list prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/MinorFormulas/MinorCoreA.lean#L24-L28

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_MinorCoreA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP PositivityTheory.Rg.Sw.SP.Mi
variable {R : Type} [CommRing R]

theorem PositivityTheory.Rg.Sw.SP.Mi.coe_list_prod {A : Type} [Ring A] [Algebra R A] (S : Subalgebra R A) (l : List S) :
    ((l.prod : S) : A) = (l.map Subtype.val).prod := by sorry
