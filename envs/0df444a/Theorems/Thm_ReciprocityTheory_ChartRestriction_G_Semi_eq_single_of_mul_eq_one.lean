-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_eq_single_of_mul_eq_one
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.eq_single_of_mul_eq_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:12.444396+00:00
-- url     : https://prove2.me/theorems/738cd1e4-d657-5696-a4d5-d6834e4d1447
-- title:
--   Semi: eq single of mul eq one
-- statement:
--   The Semi construction uses the eq single of mul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsaRos.lean#L8-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SemiabelianSchemes/PrecompleteBases/PsaRos.lean#L8-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusIsCommMonObjSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsaRos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AddMonoidAlgebra
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

theorem ReciprocityTheory.ChartRestriction.G.Semi.eq_single_of_mul_eq_one {R A : Type*} [CommRing R] [IsDomain R] [AddCommMonoid A]
    [TwoUniqueSums A] {f g : AddMonoidAlgebra R A} (h : f * g = 1) :
    ∃ a b : A, a + b = 0 ∧ f.coeff a * g.coeff b = 1 ∧
      f = single a (f.coeff a) ∧ g = single b (g.coeff b) := by sorry
