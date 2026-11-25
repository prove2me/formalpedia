-- Prove2me | Theorems.Thm_PositivityTheory_Lord_meromorphicAt_prod
-- name    : PositivityTheory.Lord.meromorphicAt_prod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:28.665626+00:00
-- url     : https://prove2.me/theorems/4f958d49-b349-4439-8007-058cec6502fa
-- title:
--   Lord: meromorphic At prod
-- statement:
--   The Lord construction uses the meromorphic At prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L105-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/MeromorphicAtProd.lean#L105-L116

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

theorem PositivityTheory.Lord.meromorphicAt_prod {ι : Type*} (t : Finset ι) (F : ι → ℂ → ℂ) (h : ∀ i ∈ t, MeromorphicAt (F i) x) :
    MeromorphicAt (fun s => ∏ i ∈ t, F i s) x := by sorry
