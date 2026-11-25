-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_smul_5019c3cbefe7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_smul_5019c3cbefe7
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:05.147485+00:00
-- url     : https://prove2.me/theorems/63faa08c-c31b-43fe-aa82-6ec9fc8ed5b6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk smul 5019c3cbefe7: P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk smul 5019c3cbefe7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk smul 5019c3cbefe7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk smul 5019c3cbefe7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L41-L42

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_smul_5019c3cbefe7 (r : R) (a : cocyDeg G deg ρ i) : Hdeg.mk (r • a) = r • Hdeg.mk a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Hdeg_mk_smul» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_smul_5019c3cbefe7
