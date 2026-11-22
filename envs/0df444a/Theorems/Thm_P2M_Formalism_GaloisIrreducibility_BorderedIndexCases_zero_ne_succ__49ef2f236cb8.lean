-- Prove2me | Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- name    : P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:13:11.52685+00:00
-- url     : https://prove2.me/theorems/7fa0ae0b-728a-483c-a248-1fbd5f8f9b41
-- title:
--   P2 M Formalism Galois Irreducibility Bordered Index Cases zero ne succ  49ef2f236cb8: P2 M Formalism Galois Irreducibility Bordered Index Cases zero ne succ  49ef2f236cb8
-- statement:
--   The P2 M Formalism Galois Irreducibility Bordered Index Cases zero ne succ  49ef2f236cb8 construction uses the P2 M Formalism Galois Irreducibility Bordered Index Cases zero ne succ  49ef2f236cb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L10-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean#L10-L10

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Matrix
open Formalism.GaloisIrreducibility.BorderedIndexCases
variable {R : Type} [CommRing R]

theorem P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8 {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := by sorry

alias «Formalism».«GaloisIrreducibility».«BorderedIndexCases».«zero_ne_succ'» := P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
