-- Prove2me | Theorems.Thm_PI_InvTopW_matrix_entries_integral
-- name    : PI.InvTopW.matrix_entries_integral
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:07.339027+00:00
-- url     : https://prove2.me/theorems/79698a9d-b715-4899-adff-3d4bbe3a73c6
-- title:
--   Inv Top W: matrix entries integral
-- statement:
--   The Inv Top W construction uses the matrix entries integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L213-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/LatticeOfEntriesIntegral.lean#L213-L229

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_LatticeOfEntriesIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)

theorem PI.InvTopW.matrix_entries_integral (I : AutInst) (c g : ℕ)
    (h1 : ∀ y ∈ I.Lf, ∀ i, (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * y i ∈ Formalism.MainNotions.S.IntAf I.F I.E)
    (h2 : ∀ u : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, u i ∈ Formalism.MainNotions.S.IntAf I.F I.E) →
      (fun i => (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * u i) ∈ I.Lf)
    (X : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))
    (hX : ∀ i j, InNInt I (g * c * c) (X i j)) (y : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (hy : y ∈ I.Lf) :
    ∃ z ∈ I.Lf, X *ᵥ y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • z := by sorry
