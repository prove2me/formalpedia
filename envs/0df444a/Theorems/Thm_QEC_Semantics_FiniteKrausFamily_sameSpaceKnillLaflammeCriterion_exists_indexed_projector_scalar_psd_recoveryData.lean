-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_psd_recoveryData
-- name    : QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_psd_recoveryData
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:15:23.268086+00:00
-- url     : https://prove2.me/theorems/24585d4d-4f28-4155-91ab-9b6323a8ca79
-- title:
--   Finite Kraus Family: same Space Knill Laflamme Criterion exists indexed projector scalar psd recovery Data
-- statement:
--   Same-space finite-Kraus KL data for complete noise has normalized projector
--   scalar data whose scalar matrix is positive semidefinite on a nonzero code.
--
--   This packages the algebraic input needed before the spectral diagonalization
--   step of the recovery construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L257-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L257-L273

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

theorem QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_exists_indexed_projector_scalar_psd_recoveryData
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (hE : E.Complete)
    (hC : C.carrier ≠ ⊥)
    (hKL : E.sameSpaceKnillLaflammeCriterion C) :
    ∃ scalar : ι → ι → Complex,
      IndexedKnillLaflammeProjectorConditionWithScalar E C scalar ∧
        (Matrix.of fun i j => scalar i j).PosSemidef ∧
        (∑ i : ι, scalar i i) • C.projector = C.projector ∧
        ∀ i j : ι, star (scalar i j) • C.projector = scalar j i • C.projector := by sorry
