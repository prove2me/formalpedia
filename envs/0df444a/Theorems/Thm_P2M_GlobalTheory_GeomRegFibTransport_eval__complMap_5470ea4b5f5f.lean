-- Prove2me | Theorems.Thm_P2M_GlobalTheory_GeomRegFibTransport_eval__complMap_5470ea4b5f5f
-- name    : P2M_GlobalTheory_GeomRegFibTransport_eval__complMap_5470ea4b5f5f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:13.975361+00:00
-- url     : https://prove2.me/theorems/24fc683f-b2bd-4095-8233-48ab75d7b576
-- title:
--   P2 M Global Theory Geom Reg Fib Transport eval  compl Map 5470ea4b5f5f: P2 M Global Theory Geom Reg Fib Transport eval  compl Map 5470ea4b5f5f
-- statement:
--   The P2 M Global Theory Geom Reg Fib Transport eval  compl Map 5470ea4b5f5f construction uses the P2 M Global Theory Geom Reg Fib Transport eval  compl Map 5470ea4b5f5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L56-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems

theorem P2M_GlobalTheory_GeomRegFibTransport_eval__complMap_5470ea4b5f5f {R S : Type} [CommRing R] [CommRing S] (e : R →+* S) (I : Ideal R)
    (J : Ideal S) (h : I.map e ≤ J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (complMap e I J h x) =
      Ideal.quotientMap (J ^ n) e (by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]; exact Ideal.pow_right_mono h n)
        (AdicCompletion.evalₐ I n x) := by sorry

alias «GlobalTheory».«GeomRegFibTransport».«evalₐ_complMap» := P2M_GlobalTheory_GeomRegFibTransport_eval__complMap_5470ea4b5f5f
