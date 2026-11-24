-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenspaceDecomposition_mem_Es
-- name    : PositivityTheory.CW.EigenspaceDecomposition.mem_Es
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:49.200611+00:00
-- url     : https://prove2.me/theorems/3cdcd831-bf5e-4fed-8717-32c9b14c541b
-- title:
--   Eigenspace Decomposition: mem Es
-- statement:
--   The Eigenspace Decomposition construction uses the mem Es property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenbasisOfBasic.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenbasisOfBasic.lean#L17-L18

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenbasisOfBasic
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
open PositivityTheory.CW.EigenspaceDecomposition
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

theorem PositivityTheory.CW.EigenspaceDecomposition.mem_Es {μ : ℝ} {v : V} : v ∈ Es ε E μ ↔ Eig ε E μ v := by sorry
