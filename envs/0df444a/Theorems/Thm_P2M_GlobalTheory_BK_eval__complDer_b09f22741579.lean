-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BK_eval__complDer_b09f22741579
-- name    : P2M_GlobalTheory_BK_eval__complDer_b09f22741579
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:01.815322+00:00
-- url     : https://prove2.me/theorems/db24e20f-0a3d-4c95-a092-20dd907da24a
-- title:
--   P2 M Global Theory BK eval  compl Der b09f22741579: P2 M Global Theory BK eval  compl Der b09f22741579
-- statement:
--   The P2 M Global Theory BK eval  compl Der b09f22741579 construction uses the P2 M Global Theory BK eval  compl Der b09f22741579 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L146-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean#L146-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology
variable {A' B : Type} [CommRing A'] [CommRing B] (ι : A' →+* B) (s : A')
variable {ι s}
variable {k : Type} [CommRing k] [Algebra k A'] (I : Ideal A') (D : Derivation k A' A')

theorem P2M_GlobalTheory_BK_eval__complDer_b09f22741579 {x : AdicCompletion I A'} {n : ℕ} {r : A'}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ r) :
    AdicCompletion.evalₐ I n (complDer I D x) = Ideal.Quotient.mk _ (D r) := by sorry

alias «GlobalTheory».«BK».«evalₐ_complDer» := P2M_GlobalTheory_BK_eval__complDer_b09f22741579
