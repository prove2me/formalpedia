-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_sigmaAt_spec_262a729a5dab
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_sigmaAt_spec_262a729a5dab
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:02.339991+00:00
-- url     : https://prove2.me/theorems/e5f2154c-2006-4256-ada2-443ba6e252a9
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Embedding holds sigma At spec 262a729a5dab: P2 M Ground Theory Heights  Heights Inter regularity Embedding holds sigma At spec 262a729a5dab
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Embedding holds sigma At spec 262a729a5dab construction uses the P2 M Ground Theory Heights  Heights Inter regularity Embedding holds sigma At spec 262a729a5dab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L92-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L92-L102

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_sigmaAt_spec_262a729a5dab {P : Ideal (MRing ι)} [P.IsPrime] {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P)
    (hne : ∀ (v : MRing ι) (a : K → ℕ), IsMultiHomog v a → v ∉ P → eval t (map (Int.castRingHom ℂ) v) ≠ 0)
    (x : funField P) {u v : MRing ι}
    (hx : (x : FractionRing (MRing ι ⧸ P)) * toFrac P v = toFrac P u) :
    sigmaAt P t ht hne x * eval t (map (Int.castRingHom ℂ) v) = eval t (map (Int.castRingHom ℂ) u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityEmbedding_holds».«sigmaAt_spec» := P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_sigmaAt_spec_262a729a5dab
