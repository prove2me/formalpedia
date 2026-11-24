-- Prove2me | Theorems.Thm_PI_GreenLabelSurjWork_glEquiv_mem_unip
-- name    : PI.GreenLabelSurjWork.glEquiv_mem_unip
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:53.737042+00:00
-- url     : https://prove2.me/theorems/45c02d57-5390-47f7-a81c-8186babf34e8
-- title:
--   Green Label Surj Work: gl Equiv mem unip
-- statement:
--   The Green Label Surj Work construction uses the gl Equiv mem unip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Transp.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GreenLabelSurjective/Transp.lean#L34-L44

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
open PI PI.GreenLabelSurjWork
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem PI.GreenLabelSurjWork.glEquiv_mem_unip {s : ℕ} (e : ι ≃ κ) (b : κ → Fin s) (u : GL ι K)
    (hu : u ∈ unip K (b ∘ e)) : glEquiv K e u ∈ unip K b := by sorry
