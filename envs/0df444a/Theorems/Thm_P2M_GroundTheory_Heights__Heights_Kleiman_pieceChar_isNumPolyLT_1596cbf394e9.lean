-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_isNumPolyLT_1596cbf394e9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_isNumPolyLT_1596cbf394e9
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:37.092269+00:00
-- url     : https://prove2.me/theorems/6310261f-de79-5ec3-8d5c-2fedb41f536c
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman piece Char is Num Poly LT 1596cbf394e9: P2 M Ground Theory Heights  Heights Kleiman piece Char is Num Poly LT 1596cbf394e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman piece Char is Num Poly LT 1596cbf394e9 construction uses the P2 M Ground Theory Heights  Heights Kleiman piece Char is Num Poly LT 1596cbf394e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L146-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapper.lean#L146-L181

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDevissageSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperHyperplaneSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperSectionSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapper
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
universe u v w
variable {k : Type u} [Field k] {N : ℕ}
variable {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_isNumPolyLT_1596cbf394e9 (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) {t : ℕ} (L : Fin t → LineBundle k x) (D : ℕ) :
    ∀ (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
      primeOf (S := k) x ≤ pp → ringKrullDim (Poly k N ⧸ pp) ≤ (D : WithBot ℕ∞) →
      ∀ a : ℤ, IsNumPolyLT t D (fun n c => (pieceChar k pp a L n c : ℚ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«pieceChar_isNumPolyLT» := P2M_GroundTheory_Heights__Heights_Kleiman_pieceChar_isNumPolyLT_1596cbf394e9
