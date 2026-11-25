-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_key_d10b44fcabab
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_key_d10b44fcabab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:02.524675+00:00
-- url     : https://prove2.me/theorems/9f4a2da0-b645-4e16-ad8a-b1778dc0737d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted key d10b44fcabab: P2 M Ground Theory Heights  Heights Field Numbers PFContracted key d10b44fcabab
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted key d10b44fcabab construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted key d10b44fcabab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L265-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L265-L361

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
variable {F K K' j ι'}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_key_d10b44fcabab (h1 : MixedDiffConst.Statement.{u}) (h2 : CutRational.Statement.{u}) :
    ∀ (n : ℕ) (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ D D0 : ℕ,
      ringKrullDim (MRing ι' F ⧸ P') = D → D ≤ n + Fintype.card K' →
      ringKrullDim (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') = D0 →
      D0 < n + Fintype.card K →
      ∀ bs : Fin n → K → ℤ, intNum F P' (fun i => pullDeg j (bs i)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«key» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_key_d10b44fcabab
