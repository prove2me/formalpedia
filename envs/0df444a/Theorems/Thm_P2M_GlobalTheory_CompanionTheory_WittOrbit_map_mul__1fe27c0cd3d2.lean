-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_WittOrbit_map_mul__1fe27c0cd3d2
-- name    : P2M_GlobalTheory_CompanionTheory_WittOrbit_map_mul__1fe27c0cd3d2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:05.944373+00:00
-- url     : https://prove2.me/theorems/77c96ed6-af28-427a-84fc-3c0e09d6f1b1
-- title:
--   P2 M Global Theory Companion Theory Witt Orbit map mul  1fe27c0cd3d2: P2 M Global Theory Companion Theory Witt Orbit map mul  1fe27c0cd3d2
-- statement:
--   The P2 M Global Theory Companion Theory Witt Orbit map mul  1fe27c0cd3d2 construction uses the P2 M Global Theory Companion Theory Witt Orbit map mul  1fe27c0cd3d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CharacterAugmentationSubspaceQuotientActionTop.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CharacterAugmentationSubspaceQuotientActionTop.lean#L27-L29

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CharacterAugmentationSubspaceQuotientActionTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WittOrbit
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}

theorem P2M_GlobalTheory_CompanionTheory_WittOrbit_map_mul__1fe27c0cd3d2 {l m n : Type} [Fintype m] (X : Matrix l m E) (Y : Matrix m n E) :
    (X * Y).map c = X.map c * Y.map c := by sorry

alias «GlobalTheory».«CompanionTheory».«WittOrbit».«map_mul'» := P2M_GlobalTheory_CompanionTheory_WittOrbit_map_mul__1fe27c0cd3d2
