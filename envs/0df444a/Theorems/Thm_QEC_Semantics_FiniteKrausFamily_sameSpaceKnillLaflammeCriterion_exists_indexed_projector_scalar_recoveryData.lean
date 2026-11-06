-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_recoveryData
-- name    : QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_recoveryData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:34:40.921031+00:00
-- url     : https://prove2.me/theorems/cdb195bd-6b5a-4916-ac89-eb8821096ae4
-- title:
--   Finite Kraus Family: same Space Knill Laflamme Criterion exists indexed projector scalar recovery Data
-- statement:
--   Same-space finite-Kraus KL data for complete noise admits indexed projector
--   scalars with the two algebraic properties needed by the recovery construction:
--   normalized diagonal sum and Hermitian symmetry on the code projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L135-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L135-L147

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

theorem QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_recoveryData
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector ∧
        ∀ i j : ι, star (scalar i j) • C.projector = scalar j i • C.projector := by sorry
