-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_eq_mk_1fa86da258c3
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_eq_mk_1fa86da258c3
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:21.568997+00:00
-- url     : https://prove2.me/theorems/3ec2bb83-1129-445f-8ea4-f8fe744b56eb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk eq mk 1fa86da258c3: P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk eq mk 1fa86da258c3
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk eq mk 1fa86da258c3 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cech Hdeg mk eq mk 1fa86da258c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCechExact.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_eq_mk_1fa86da258c3 (z z' : cocyDeg G deg ρ i) :
    Hdeg.mk z = Hdeg.mk z' ↔ z.1 - z'.1 ∈ bdryDeg G deg ρ i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«Cech».«Hdeg_mk_eq_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_Cech_Hdeg_mk_eq_mk_1fa86da258c3
