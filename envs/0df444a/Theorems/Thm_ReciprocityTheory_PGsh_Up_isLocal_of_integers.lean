-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_isLocal_of_integers
-- name    : ReciprocityTheory.PGsh.Up.isLocal_of_integers
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:24.278612+00:00
-- url     : https://prove2.me/theorems/d796a33b-92f5-421e-8dfa-ff07a78bbf5f
-- title:
--   Up: is Local of integers
-- statement:
--   The Up construction uses the is Local of integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsLocalOfIntegers.lean#L161-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsLocalOfIntegers.lean#L161-L172

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up

theorem ReciprocityTheory.PGsh.Up.isLocal_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) : IsLocalRing R := by sorry
