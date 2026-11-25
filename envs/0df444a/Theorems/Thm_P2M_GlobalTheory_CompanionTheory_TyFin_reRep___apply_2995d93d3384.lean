-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_TyFin_reRep___apply_2995d93d3384
-- name    : P2M_GlobalTheory_CompanionTheory_TyFin_reRep___apply_2995d93d3384
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:05:54.33355+00:00
-- url     : https://prove2.me/theorems/2586e8bd-6396-430f-9fcf-8a74ed1d7777
-- title:
--   P2 M Global Theory Companion Theory Ty Fin re Rep   apply 2995d93d3384: P2 M Global Theory Companion Theory Ty Fin re Rep   apply 2995d93d3384
-- statement:
--   The P2 M Global Theory Companion Theory Ty Fin re Rep   apply 2995d93d3384 construction uses the P2 M Global Theory Companion Theory Ty Fin re Rep   apply 2995d93d3384 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalIsomorphismProperties.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalIsomorphismProperties.lean#L35-L37

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
omit [Fintype K] [DecidableEq K]

theorem P2M_GlobalTheory_CompanionTheory_TyFin_reRep___apply_2995d93d3384 (e : α ≃ β) (τ : FDRep ℂ (GL α K)) (g : GL β K) :
    (reRep e τ).ρ g = τ.ρ ((glEquiv K e).symm g) := by sorry

alias «GlobalTheory».«CompanionTheory».«TyFin».«reRep_ρ_apply» := P2M_GlobalTheory_CompanionTheory_TyFin_reRep___apply_2995d93d3384
