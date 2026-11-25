-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_archUnitary_preserves_form_29e3039d0c28
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_archUnitary_preserves_form_29e3039d0c28
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:34.690734+00:00
-- url     : https://prove2.me/theorems/69339751-4611-4c46-9e9e-e0adead27236
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume arch Unitary preserves form 29e3039d0c28: P2 M Ground Theory Heights  Heights Finite Covolume arch Unitary preserves form 29e3039d0c28
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume arch Unitary preserves form 29e3039d0c28 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume arch Unitary preserves form 29e3039d0c28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentHorizontal.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentHorizontal.lean#L23-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipotentHorizontal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StRationalUnipotent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StUnipRadicalOfRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementArchCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMahlerCompactness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PArchInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentHorizontal
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
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_archUnitary_preserves_form_29e3039d0c28 (h : HermitianForm F E W) (v : Basis ι E W)
    (g : archUnitary h v) (w : InfinitePlace E) (a b : ι → ℂ) :
    star (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ a) ⬝ᵥ
        (gramAt h v w *ᵥ (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ b)) =
      star a ⬝ᵥ (gramAt h v w *ᵥ b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«archUnitary_preserves_form» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_archUnitary_preserves_form_29e3039d0c28
