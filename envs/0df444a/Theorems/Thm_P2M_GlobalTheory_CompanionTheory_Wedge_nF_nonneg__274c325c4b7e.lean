-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Wedge_nF_nonneg__274c325c4b7e
-- name    : P2M_GlobalTheory_CompanionTheory_Wedge_nF_nonneg__274c325c4b7e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:52.604042+00:00
-- url     : https://prove2.me/theorems/07cda9d5-8e55-43a4-bfbe-63c7f5f36b67
-- title:
--   P2 M Global Theory Companion Theory Wedge n F nonneg  274c325c4b7e: P2 M Global Theory Companion Theory Wedge n F nonneg  274c325c4b7e
-- statement:
--   The P2 M Global Theory Companion Theory Wedge n F nonneg  274c325c4b7e construction uses the P2 M Global Theory Companion Theory Wedge n F nonneg  274c325c4b7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L12-L13

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]

theorem P2M_GlobalTheory_CompanionTheory_Wedge_nF_nonneg__274c325c4b7e [Fintype κ] [DecidableEq κ] (A : Matrix ι κ K) : 0 ≤ nF A := by sorry

alias «GlobalTheory».«CompanionTheory».«Wedge».«nF_nonneg'» := P2M_GlobalTheory_CompanionTheory_Wedge_nF_nonneg__274c325c4b7e
