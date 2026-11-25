-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_zero_7e32b064706a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_zero_7e32b064706a
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:36:00.91455+00:00
-- url     : https://prove2.me/theorems/98bd65b9-560b-52cc-9f35-f2896fe4aeea
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk zero 7e32b064706a: P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk zero 7e32b064706a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk zero 7e32b064706a construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk zero 7e32b064706a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L35-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.Kleiman.Cech
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {deg : ∀ I, Submodule R (G I)}
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J} {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_zero_7e32b064706a : Hdeg.mk (0 : cocyDeg G deg ρ i) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Hdeg_mk_zero» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_zero_7e32b064706a
