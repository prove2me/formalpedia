-- Prove2me | Theorems.Thm_PositivityTheory_CWB_WordFiltrationCommute_U_mono
-- name    : PositivityTheory.CWB.WordFiltrationCommute.U_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:51:23.369385+00:00
-- url     : https://prove2.me/theorems/bb616bb2-f6b8-42b1-bb9f-b4f0c0e83dd9
-- title:
--   Word Filtration Commute: U mono
-- statement:
--   The Word Filtration Commute construction uses the U mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/U0Commute.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/U0Commute.lean#L19-L20

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryGroupStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ParabolicUnipotentGL
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_U0Commute
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
open PositivityTheory PositivityTheory.CWB
open PositivityTheory.CW
open PositivityTheory.CWB.WordFiltrationCommute
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

theorem PositivityTheory.CWB.WordFiltrationCommute.U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by sorry
