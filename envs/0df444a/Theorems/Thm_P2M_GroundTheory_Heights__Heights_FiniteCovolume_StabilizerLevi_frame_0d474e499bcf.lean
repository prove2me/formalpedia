-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_frame_0d474e499bcf
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_frame_0d474e499bcf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:52.966553+00:00
-- url     : https://prove2.me/theorems/f0362e07-e391-4fa4-bcc7-bfb7b3cf0787
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi frame 0d474e499bcf: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi frame 0d474e499bcf
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi frame 0d474e499bcf construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi frame 0d474e499bcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L88-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L88-L130

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {x₀ w₀ : W} {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_frame_0d474e499bcf (v : Basis ι E W) (hp : IsHyperbolicPair h x₀ w₀)
    (h' : HermitianForm F E (hypComplement h x₀ w₀)) (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y)
    (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    (gramAt h v w)ᴴ = gramAt h v w ∧
    IsUnit ((colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w).det ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1 ∧
    ∀ z, ∃ (a b : ℂ) (c : Fin n → ℂ), z = a • vecAt v x₀ w + b • vecAt v w₀ w +
      colMat v (fun k => (v' k : W)) w *ᵥ c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«frame» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_frame_0d474e499bcf
