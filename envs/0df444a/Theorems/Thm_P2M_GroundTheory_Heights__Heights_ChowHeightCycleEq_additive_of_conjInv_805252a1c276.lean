-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_of_conjInv_805252a1c276
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_of_conjInv_805252a1c276
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:06.197246+00:00
-- url     : https://prove2.me/theorems/6c785319-4a27-434c-834d-b586b8a6cb3f
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Cycle Eq additive of conj Inv 805252a1c276: P2 M Ground Theory Heights  Heights Chow Height Cycle Eq additive of conj Inv 805252a1c276
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Cycle Eq additive of conj Inv 805252a1c276 construction uses the P2 M Ground Theory Heights  Heights Chow Height Cycle Eq additive of conj Inv 805252a1c276 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L119-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L119-L136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_of_conjInv_805252a1c276 (hA : ChowHeightMul.Statement) {K : Type} [Field K] [NumberField K]
    (T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hT : ∀ w, IsUnit (T w))
    (hreal : ∀ w : InfinitePlace K, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (δ₁ δ₂ : ℕ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) (f * g)
        (δ₁ + δ₂) =
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) f δ₁ +
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) g δ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightCycleEq».«additive_of_conjInv» := P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_of_conjInv_805252a1c276
