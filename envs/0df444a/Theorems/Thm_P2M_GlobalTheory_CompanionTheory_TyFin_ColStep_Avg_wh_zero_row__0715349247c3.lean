-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_wh_zero_row__0715349247c3
-- name    : P2M_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_wh_zero_row__0715349247c3
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:47.275619+00:00
-- url     : https://prove2.me/theorems/dc6e0802-a54e-4058-8c7e-2b1297fcd42b
-- title:
--   P2 M Global Theory Companion Theory Ty Fin Col Step Avg wh zero row  0715349247c3: P2 M Global Theory Companion Theory Ty Fin Col Step Avg wh zero row  0715349247c3
-- statement:
--   The P2 M Global Theory Companion Theory Ty Fin Col Step Avg wh zero row  0715349247c3 construction uses the P2 M Global Theory Companion Theory Ty Fin Col Step Avg wh zero row  0715349247c3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L143-L148

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {d j : ℕ}

theorem P2M_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_wh_zero_row__0715349247c3 : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ),
    (∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) →
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by sorry

alias «GlobalTheory».«CompanionTheory».«TyFin».«ColStep».«Avg».«wh_zero_row'» := P2M_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_wh_zero_row__0715349247c3
