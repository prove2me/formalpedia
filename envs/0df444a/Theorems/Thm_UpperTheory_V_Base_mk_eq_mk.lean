-- Prove2me | Theorems.Thm_UpperTheory_V_Base_mk_eq_mk
-- name    : UpperTheory.V.Base.mk_eq_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:44:43.510832+00:00
-- url     : https://prove2.me/theorems/7be2f314-6034-468c-8d0d-073c82117dcf
-- title:
--   Base: mk eq mk
-- statement:
--   The Base construction uses the mk eq mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean#L50-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.Gal
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem UpperTheory.V.Base.mk_eq_mk (ρ : Representation R G M) (U : Subgroup G) (z z' : Z1U ρ U) :
    (Submodule.Quotient.mk z : H1U ρ U) = Submodule.Quotient.mk z' ↔
      ∃ m, ∀ u : U, z.1 u - z'.1 u = ρ u m - m := by sorry
