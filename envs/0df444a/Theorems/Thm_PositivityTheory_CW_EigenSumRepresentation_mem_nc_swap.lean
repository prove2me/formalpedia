-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenSumRepresentation_mem_nc_swap
-- name    : PositivityTheory.CW.EigenSumRepresentation.mem_nc_swap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:03.690332+00:00
-- url     : https://prove2.me/theorems/6caca32f-842f-418d-b794-59f522b9e804
-- title:
--   Eigen Sum Representation: mem nc swap
-- statement:
--   The Eigen Sum Representation construction uses the mem nc swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/WordFiltrationCommute.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/WordFiltrationCommute.lean#L70-L72

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_WordFiltrationCommute
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
open PositivityTheory.CW.EigenSumRepresentation
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}

theorem PositivityTheory.CW.EigenSumRepresentation.mem_nc_swap {p : Fin n × Fin n} (hp : p ∈ nc ε) : p.swap ∈ nc ε := by sorry
