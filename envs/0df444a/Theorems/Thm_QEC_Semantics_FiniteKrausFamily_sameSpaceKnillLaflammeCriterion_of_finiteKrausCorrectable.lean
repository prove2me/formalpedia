-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
-- name    : QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:46:07.789606+00:00
-- url     : https://prove2.me/theorems/b849f3e9-89b4-44be-9310-90eed1dfaabf
-- title:
--   Finite Kraus Family: same Space Knill Laflamme Criterion of finite Kraus Correctable
-- statement:
--   KL96 forward direction for the project finite-dimensional same-space
--   finite-Kraus semantics.
--
--   Correctability by an arbitrary CPTP `QuantumChannel` recovery implies the
--   same-space finite-Kraus Knill-Laflamme condition.  The proof first chooses a
--   finite Kraus representation of the recovery channel, transports the exact
--   correction equation through that representation, applies the KL96 branch-scalar
--   bridge, and then runs the explicit branch-scalar KL calculation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L502-L530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L502-L530

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

theorem QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_of_finiteKrausCorrectable
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (recovery : QuantumChannel H H)
    (h : FiniteKrausCorrectable ι H H C E recovery) :
    E.sameSpaceKnillLaflammeCriterion C := by sorry
