-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KAway_cond_c
-- name    : PositivityTheory.SiegelWeilFormula.KAway.cond_c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:57:02.570609+00:00
-- url     : https://prove2.me/theorems/fbb683d9-0387-4680-bc59-8ca647c7031b
-- title:
--   KAway: cond c
-- statement:
--   The KAway construction uses the cond c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L111-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L111-L137

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
variable (c : R →+* R) (ε : ℤ)

theorem PositivityTheory.SiegelWeilFormula.KAway.cond_c (A C : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) (hε : ε * ε = 1)
    (h : Aᵀ * C.map c + (ε : R) • (Cᵀ * A.map c) = 0) (ε₁ : ℤ) :
    ((ε₁ : R) • (C * A⁻¹))ᵀ + (ε : R) • ((ε₁ : R) • (C * A⁻¹)).map c = 0 := by sorry
