-- Prove2me | Theorems.Thm_PositivityTheory_Lord_hasProd_compl_finset
-- name    : PositivityTheory.Lord.hasProd_compl_finset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:29.208354+00:00
-- url     : https://prove2.me/theorems/ff9ac30d-7613-44aa-a2e1-15403d00e37c
-- title:
--   Lord: has Prod compl finset
-- statement:
--   The Lord construction uses the has Prod compl finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FinMod.lean#L5-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ZetaEulerProducts/FinMod.lean#L5-L37

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ZetaEulerProducts_FinMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Lord

theorem PositivityTheory.Lord.hasProd_compl_finset {ι : Type*} [DecidableEq ι] (f g : ι → ℂ) (a : ℂ) (T S : Finset ι) (hST : S ⊆ T)
    (hg : HasProd g a) (hg0 : ∀ v ∈ T, g v ≠ 0) (hfg : ∀ v, v ∉ T → f v = g v) :
    HasProd (fun v : {v // v ∉ S} => f v) (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by sorry
