-- Prove2me | Theorems.Thm_PositivityTheory_CW_CasimirRealScalar_term_im
-- name    : PositivityTheory.CW.CasimirRealScalar.term_im
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:24.369428+00:00
-- url     : https://prove2.me/theorems/7a304cfe-12e5-4ee5-bdd7-1d3059a2bbe8
-- title:
--   Casimir Real Scalar: term im
-- statement:
--   The Casimir Real Scalar construction uses the term im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CasimirRealOfCentral.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/CasimirRealOfCentral.lean#L19-L28

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_CasimirRealOfCentral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.CasimirRealScalar
variable {n : ℕ}

theorem PositivityTheory.CW.CasimirRealScalar.term_im {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E) (a b : Fin n) (v : V) :
    (inner ℂ v (E a b (E b a v))).im = 0 := by sorry
