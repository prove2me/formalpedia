-- Prove2me | Theorems.Thm_P2M_GlobalTheory_JR_ImgSec_hankel_apply__cc3892b32a9c
-- name    : P2M_GlobalTheory_JR_ImgSec_hankel_apply__cc3892b32a9c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:50.854814+00:00
-- url     : https://prove2.me/theorems/3df57f6e-1361-4bfe-bfdc-c1bcbd99655e
-- title:
--   P2 M Global Theory JR Img Sec hankel apply  cc3892b32a9c: P2 M Global Theory JR Img Sec hankel apply  cc3892b32a9c
-- statement:
--   The P2 M Global Theory JR Img Sec hankel apply  cc3892b32a9c construction uses the P2 M Global Theory JR Img Sec hankel apply  cc3892b32a9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CompanionMatrixOfCoeffsPowMulVecFirstBasisVector.lean#L30-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ImgSec
variable {k : Type} [CommRing k] {r : ℕ}

theorem P2M_GlobalTheory_JR_ImgSec_hankel_apply__cc3892b32a9c (a : Inv r k) (i j : Fin r) : hankel a i j = (a.2.1 ᵥ* (companion a.1 ^ (i : ℕ))) j := by sorry

alias «GlobalTheory».«JR».«ImgSec».«hankel_apply'» := P2M_GlobalTheory_JR_ImgSec_hankel_apply__cc3892b32a9c
