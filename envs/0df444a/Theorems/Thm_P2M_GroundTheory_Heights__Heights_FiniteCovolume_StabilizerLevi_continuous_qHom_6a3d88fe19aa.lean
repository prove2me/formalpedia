-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_qHom_6a3d88fe19aa
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_qHom_6a3d88fe19aa
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:37:25.232787+00:00
-- url     : https://prove2.me/theorems/9089c4dd-bc0c-4015-b3d6-298df71d9c6b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi continuous q Hom 6a3d88fe19aa: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi continuous q Hom 6a3d88fe19aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi continuous q Hom 6a3d88fe19aa construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi continuous q Hom 6a3d88fe19aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLevi.lean#L137-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLevi.lean#L137-L147

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W} {n : ℕ}
  (hp : IsHyperbolicPair h x₀ w₀) {h' : HermitianForm F E (hypComplement h x₀ w₀)}
  (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) {v' : Basis (Fin n) E (hypComplement h x₀ w₀)}
include hp hh'

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_qHom_6a3d88fe19aa : Continuous (qHom hp hh' (v := v) (v' := v')) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«continuous_qHom» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_continuous_qHom_6a3d88fe19aa
