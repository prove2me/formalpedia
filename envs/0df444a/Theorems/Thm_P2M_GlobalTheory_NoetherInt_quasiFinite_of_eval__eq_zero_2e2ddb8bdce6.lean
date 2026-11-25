-- Prove2me | Theorems.Thm_P2M_GlobalTheory_NoetherInt_quasiFinite_of_eval__eq_zero_2e2ddb8bdce6
-- name    : P2M_GlobalTheory_NoetherInt_quasiFinite_of_eval__eq_zero_2e2ddb8bdce6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:07:04.189351+00:00
-- url     : https://prove2.me/theorems/a1d3b7dc-6ee5-47a1-9031-04e1232d3665
-- title:
--   P2 M Global Theory Noether Int quasi Finite of eval  eq zero 2e2ddb8bdce6: P2 M Global Theory Noether Int quasi Finite of eval  eq zero 2e2ddb8bdce6
-- statement:
--   The P2 M Global Theory Noether Int quasi Finite of eval  eq zero 2e2ddb8bdce6 construction uses the P2 M Global Theory Noether Int quasi Finite of eval  eq zero 2e2ddb8bdce6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L36-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsQuasiFinitePolynomialMap.lean#L36-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open Polynomial

theorem P2M_GlobalTheory_NoetherInt_quasiFinite_of_eval__eq_zero_2e2ddb8bdce6 {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (t : T)
    (h : (eval₂RingHom φ t).QuasiFinite) (G : R[X]) (hG : eval₂ φ t G = 0) (k : ℕ)
    (hc : IsUnit (G.coeff k)) : φ.QuasiFinite := by sorry

alias «GlobalTheory».«NoetherInt».«quasiFinite_of_eval₂_eq_zero» := P2M_GlobalTheory_NoetherInt_quasiFinite_of_eval__eq_zero_2e2ddb8bdce6
