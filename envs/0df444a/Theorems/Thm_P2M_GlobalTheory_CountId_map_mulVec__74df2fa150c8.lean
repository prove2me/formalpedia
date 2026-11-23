-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CountId_map_mulVec__74df2fa150c8
-- name    : P2M_GlobalTheory_CountId_map_mulVec__74df2fa150c8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:51.261808+00:00
-- url     : https://prove2.me/theorems/9c51d10c-5e1e-43dd-8c7b-b953333a79e0
-- title:
--   P2 M Global Theory Count Id map mul Vec  74df2fa150c8: P2 M Global Theory Count Id map mul Vec  74df2fa150c8
-- statement:
--   The P2 M Global Theory Count Id map mul Vec  74df2fa150c8 construction uses the P2 M Global Theory Count Id map mul Vec  74df2fa150c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k']

theorem P2M_GlobalTheory_CountId_map_mulVec__74df2fa150c8 (φ : k →+* k') (A : Matrix (Fin r) (Fin r) k) (v : Fin r → k) :
    (fun i => φ ((A *ᵥ v) i)) = A.map φ *ᵥ fun i => φ (v i) := by sorry

alias «GlobalTheory».«CountId».«map_mulVec'» := P2M_GlobalTheory_CountId_map_mulVec__74df2fa150c8
