-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueBundles_localPiece_b8db47c49997
-- name    : P2M_GroundTheory_Heights__Heights_Model_GlueBundles_localPiece_b8db47c49997
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:45.157251+00:00
-- url     : https://prove2.me/theorems/cfa04d97-2c8a-48e7-9cc8-8d7687341e70
-- title:
--   P2 M Ground Theory Heights  Heights Model Glue Bundles local Piece b8db47c49997: P2 M Ground Theory Heights  Heights Model Glue Bundles local Piece b8db47c49997
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Glue Bundles local Piece b8db47c49997 construction uses the P2 M Ground Theory Heights  Heights Model Glue Bundles local Piece b8db47c49997 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L41-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PGlueBundles.lean#L41-L177

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueCoherence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}

theorem P2M_GroundTheory_Heights__Heights_Model_GlueBundles_localPiece_b8db47c49997 (hSB : SpreadBundle.Statement) (hSI : SpreadIso.Statement)
    (hVR : VectorBundleRestrict.Statement) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f]
    (S : Finset Nat.Primes) (E₀ : (invOpen f (primeProd S) : Scheme.{0}).Modules)
    (hE₀ : IsVectorBundle E₀) (p : S) (Ep : (baseChange f (ZLoc p)).Modules) (hEp : IsVectorBundle Ep)
    (β : (Scheme.Modules.pullback (ratToLoc f p)).obj Ep ≅
      (Scheme.Modules.pullback (toInvOpen f ℚ (primeProd S)
        (isUnit_intCast_rat _ (primeProd_ne_zero S)))).obj E₀) :
    ∃ (n : ℕ) (hn : ¬ (((p : Nat.Primes) : ℕ) : ℤ) ∣ (n : ℤ)),
      (∀ q ∈ S, q ≠ (p : Nat.Primes) → ((q : ℕ) : ℤ) ∣ (n : ℤ)) ∧
      ∃ (F : (invOpen f n : Scheme.{0}).Modules), IsVectorBundle F ∧
      ∃ (ψ' : (Scheme.Modules.pullback (X.homOfLE
            (inf_le_left : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n))).obj F ≅
          (Scheme.Modules.pullback (X.homOfLE
            (inf_le_right : invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S)))).obj E₀)
        (δ : (Scheme.Modules.pullback (toInvOpen f (ZLoc p) n (isUnit_intCast_zLoc p n hn))).obj F ≅ Ep),
      ∀ (E : X.Modules) (e₀ : (Scheme.Modules.pullback (invOpen f (primeProd S)).ι).obj E ≅ E₀)
        (eU : (Scheme.Modules.pullback (invOpen f n).ι).obj E ≅ F),
        pullbackCompIso (X.homOfLE_ι (inf_le_right :
            invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f (primeProd S))) e₀ =
          pullbackCompIso (X.homOfLE_ι (inf_le_left :
            invOpen f n ⊓ invOpen f (primeProd S) ≤ invOpen f n)) eU ≪≫ ψ' →
        pullbackCompIso (toInvOpen_ι f ℚ (primeProd S)
            (isUnit_intCast_rat _ (primeProd_ne_zero S))) e₀ =
          pullbackCompIso (ratToLoc_baseChangeMap f p)
            (pullbackCompIso (toInvOpen_ι f (ZLoc p) n (isUnit_intCast_zLoc p n hn)) eU ≪≫ δ) ≪≫ β := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«GlueBundles».«localPiece» := P2M_GroundTheory_Heights__Heights_Model_GlueBundles_localPiece_b8db47c49997
