-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_exists_indexed_scalar_complete_diagonal_sum
-- name    : QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_scalar_complete_diagonal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:34:31.743221+00:00
-- url     : https://prove2.me/theorems/f0b2ceb2-bff9-4688-abfe-cf31fc44c8a9
-- title:
--   Finite Kraus Family: same Space Knill Laflamme Criterion exists indexed scalar complete diagonal sum
-- statement:
--   Same-space finite-Kraus KL data can be represented by indexed scalars whose
--   diagonal sum is normalized on the code projector whenever the noise is complete.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L118-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L118-L128

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_scalar_complete_diagonal_sum
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeConditionWithScalar E C scalar ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector := by sorry
