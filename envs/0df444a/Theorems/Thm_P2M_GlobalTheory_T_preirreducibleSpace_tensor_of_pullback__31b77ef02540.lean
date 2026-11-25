-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_preirreducibleSpace_tensor_of_pullback__31b77ef02540
-- name    : P2M_GlobalTheory_T_preirreducibleSpace_tensor_of_pullback__31b77ef02540
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:35.453596+00:00
-- url     : https://prove2.me/theorems/04ea32b6-b511-4470-adb2-8c4d886f3ff6
-- title:
--   P2 M Global Theory T preirreducible Space tensor of pullback  31b77ef02540: P2 M Global Theory T preirreducible Space tensor of pullback  31b77ef02540
-- statement:
--   The P2 M Global Theory T preirreducible Space tensor of pullback  31b77ef02540 construction uses the P2 M Global Theory T preirreducible Space tensor of pullback  31b77ef02540 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceTensorOfPullbackStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleSpaceTensorOfPullbackStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullbackStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_preirreducibleSpace_tensor_of_pullback__31b77ef02540 : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k] [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom → PreirreducibleSpace ↥(pullback (W.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by sorry

alias «GlobalTheory».«T».«preirreducibleSpace_tensor_of_pullback'» := P2M_GlobalTheory_T_preirreducibleSpace_tensor_of_pullback__31b77ef02540
