-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_length_baseChange_eq
-- name    : ReciprocityTheory.ChartRestriction.G.T0.length_baseChange_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:42.826854+00:00
-- url     : https://prove2.me/theorems/f7c83b59-10b9-41e0-b9cb-26cf659f2443
-- title:
--   T0: length base Change eq
-- statement:
--   The T0 construction uses the length base Change eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FlatLength.lean#L104-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FlatLength.lean#L104-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FlatLength
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

theorem ReciprocityTheory.ChartRestriction.G.T0.length_baseChange_eq {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [Algebra R S] [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    (hm : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Module.length S (S ⊗[R] Q) = Module.length R Q := by sorry
