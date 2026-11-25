-- Prove2me | Theorems.Thm_P2M_GlobalTheory_LocalFiniteOddFixed_norm_prod__35ea87ad5dd5
-- name    : P2M_GlobalTheory_LocalFiniteOddFixed_norm_prod__35ea87ad5dd5
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:06:51.316569+00:00
-- url     : https://prove2.me/theorems/74da61bc-928d-4f2a-9517-9b8045f6aa92
-- title:
--   P2 M Global Theory Local Finite Odd Fixed norm prod  35ea87ad5dd5: P2 M Global Theory Local Finite Odd Fixed norm prod  35ea87ad5dd5
-- statement:
--   The P2 M Global Theory Local Finite Odd Fixed norm prod  35ea87ad5dd5 construction uses the P2 M Global Theory Local Finite Odd Fixed norm prod  35ea87ad5dd5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L304-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsLocalRingOfFinite.lean#L304-L308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
open GlobalTheory.UnitLemma

theorem P2M_GlobalTheory_LocalFiniteOddFixed_norm_prod__35ea87ad5dd5 (E A B : Type) [Field E] [CommRing A] [CommRing B] [Algebra E A] [Algebra E B]
    [Module.Finite E A] [Module.Finite E B] (a : A) (b : B) :
    Algebra.norm E ((a, b) : A × B) = Algebra.norm E a * Algebra.norm E b := by sorry

alias «GlobalTheory».«LocalFiniteOddFixed».«norm_prod'» := P2M_GlobalTheory_LocalFiniteOddFixed_norm_prod__35ea87ad5dd5
