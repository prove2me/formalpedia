-- Prove2me | Theorems.Thm_PositivityTheory_CW_EigenspaceOrthogonality_nc_sum
-- name    : PositivityTheory.CW.EigenspaceOrthogonality.nc_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:49:59.248889+00:00
-- url     : https://prove2.me/theorems/e1f5a0a4-20bc-4e7a-a628-51090994e587
-- title:
--   Eigenspace Orthogonality: nc sum
-- statement:
--   The Eigenspace Orthogonality construction uses the nc sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/EigenspacesOrthogonalOfCalculus.lean#L14-L17

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_EigenspacesOrthogonalOfCalculus
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
open PositivityTheory.CW.EigenspaceOrthogonality
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}

theorem PositivityTheory.CW.EigenspaceOrthogonality.nc_sum (f : Fin n × Fin n → ℂ) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε a ≠ ε b then f (a, b) else 0 := by sorry
