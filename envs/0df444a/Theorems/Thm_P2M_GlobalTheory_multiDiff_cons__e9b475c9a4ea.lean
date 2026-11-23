-- Prove2me | Theorems.Thm_P2M_GlobalTheory_multiDiff_cons__e9b475c9a4ea
-- name    : P2M_GlobalTheory_multiDiff_cons__e9b475c9a4ea
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:08.403993+00:00
-- url     : https://prove2.me/theorems/3a500c10-0cc9-4c3b-a465-39398dd898a8
-- title:
--   P2 M Global Theory multi Diff cons  e9b475c9a4ea: P2 M Global Theory multi Diff cons  e9b475c9a4ea
-- statement:
--   The P2 M Global Theory multi Diff cons  e9b475c9a4ea construction uses the P2 M Global Theory multi Diff cons  e9b475c9a4ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L91-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

theorem P2M_GlobalTheory_multiDiff_cons__e9b475c9a4ea {d : ℕ} (a : G) (g : Fin d → G) (φ : G → M) :
    multiDiff (Fin.cons a g : Fin (d + 1) → G) φ = multiDiff g (bwdDiff a φ) := by sorry

alias «GlobalTheory».«multiDiff_cons'» := P2M_GlobalTheory_multiDiff_cons__e9b475c9a4ea
