-- Prove2me | Theorems.Thm_ULHC_walk_local
-- name    : ULHC.walk_local
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:47:46.904802+00:00
-- url     : https://prove2.me/theorems/5fc1f456-2351-46a4-a2c5-069495317b16
-- title:
--   ULHC: walk local
-- statement:
--   The ULHC construction uses the walk local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L70-L83
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/Walk.lean#L70-L83

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
set_option autoImplicit true
open ULHC
open Finset Classical

theorem ULHC.walk_local : ∀ (mb mt ml mr pbl pbr ptl ptr q o : Bool) (si : Side),
    (∀ s, mS mb mt ml mr s = true → cutS pbl pbr ptl ptr s = false) →
    (∀ s, cutS pbl pbr ptl ptr s = true →
        (mS mb mt ml mr (latA s) || mS mb mt ml mr (latB s)) = true) →
    ((mb == mt) && (ml == mr) && (mb != ml) = true → ∀ s, cutS pbl pbr ptl ptr s = false) →
    cutS pbl pbr ptl ptr si = true → outS q (mS mb mt ml mr) si = !o →
    (∃ so, so ≠ si ∧ cutS pbl pbr ptl ptr so = true ∧ outS q (mS mb mt ml mr) so = o ∧
        ∀ s', cutS pbl pbr ptl ptr s' = true → outS q (mS mb mt ml mr) s' = !o → s' = si) ∨
    (∃ d, mS mb mt ml mr d = true ∧ mS mb mt ml mr d.opp = false ∧
        mS mb mt ml mr (latA d) = false ∧ mS mb mt ml mr (latB d) = false ∧
        (si = latA d ∨ si = latB d) ∧ cutS pbl pbr ptl ptr d.opp = false ∧
        outS q (mS mb mt ml mr) d.opp = o ∧
        ∀ s, cutS pbl pbr ptl ptr s = true → outS q (mS mb mt ml mr) s = !o) := by sorry
