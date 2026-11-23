-- Prove2me | Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_right
-- name    : UpperTheory.V.U3.unitaryThreeReflection_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:30.133238+00:00
-- url     : https://prove2.me/theorems/075c8292-4df8-4db4-86db-9ffa3ecc2860
-- title:
--   U3: unitary Three Reflection right
-- statement:
--   The U3 construction uses the unitary Three Reflection right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/UnitaryThreeReflectionRight.lean#L299-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/UnitaryThreeReflectionRight.lean#L299-L299

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_UnitaryThreeReflectionRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.V UpperTheory.V.U3
open Matrix
variable {R : Type*} [CommRing R]
variable {G : Type*} [Group G]

theorem UpperTheory.V.U3.unitaryThreeReflection_right (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G) : (r0 η Ψ g).right = η g := by sorry

attribute [defeq] UpperTheory.V.U3.unitaryThreeReflection_right
