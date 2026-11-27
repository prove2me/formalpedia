-- Prove2me | Theorems.Thm_PositivityTheory_Lord_ZO_prod
-- name    : PositivityTheory.Lord.ZO.prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:49:58.262717+00:00
-- url     : https://prove2.me/theorems/7650040c-8121-4fe5-84f1-4476ff179706
-- title:
--   ZO: prod
-- statement:
--   The ZO construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L84-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L84-L95

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_MeromorphicAtProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open PositivityTheory PositivityTheory.Lord
variable {f g : ℂ → ℂ} {x : ℂ} {k l m n : ℕ}

theorem PositivityTheory.Lord.ZO.prod {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (K : ι → ℕ) (h : ∀ i ∈ t, ZO (F i) x (K i)) :
    ZO (fun s => ∏ i ∈ t, F i s) x (∑ i ∈ t, K i) := by sorry
