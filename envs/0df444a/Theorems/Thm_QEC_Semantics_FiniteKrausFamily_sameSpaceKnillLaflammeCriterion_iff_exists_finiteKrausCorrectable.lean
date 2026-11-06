-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_exists_finiteKrausCorrectable
-- name    : QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_finiteKrausCorrectable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:18:28.092317+00:00
-- url     : https://prove2.me/theorems/b3a2388f-3c68-4b93-bea2-e47fd4f13ea3
-- title:
--   Finite Kraus Family: same Space Knill Laflamme Criterion iff exists finite Kraus Correctable
-- statement:
--   KL96 equivalence for the project finite-dimensional same-space finite-Kraus
--   semantics.
--
--   A complete finite Kraus family satisfies the Knill-Laflamme condition on a
--   quantum code iff there exists an arbitrary CPTP `QuantumChannel` recovery that
--   makes the code correctable for that family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1636-L1644
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1636-L1644

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

theorem QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_exists_finiteKrausCorrectable
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (hE : E.Complete) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      ∃ recovery : QuantumChannel H H, FiniteKrausCorrectable ι H H C E recovery := by sorry
