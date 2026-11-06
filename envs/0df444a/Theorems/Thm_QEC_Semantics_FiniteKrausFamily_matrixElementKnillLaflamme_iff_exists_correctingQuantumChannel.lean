-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
-- name    : QEC.Semantics.FiniteKrausFamily.matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:47:25.082015+00:00
-- url     : https://prove2.me/theorems/ff7cfa80-b6c7-41e7-9658-edb517acd8f8
-- title:
--   Finite Kraus Family: matrix Element Knill Laflamme iff exists correcting Quantum Channel
-- statement:
--   The finite-dimensional same-space Knill-Laflamme criterion with both sides
--   expanded for public use.
--
--   For a complete finite Kraus family, the indexed matrix-element condition is
--   equivalent to existence of a CPTP recovery that reverses its operator-sum map
--   on every density operator supported on the code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1654-L1678
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L1654-L1678

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

theorem QEC.Semantics.FiniteKrausFamily.matrixElementKnillLaflamme_iff_exists_correctingQuantumChannel
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (hE : E.Complete) :
    (∃ scalar : ι → ι → Complex,
      ∀ i j : ι,
        ∀ x : H, x ∈ C.carrier →
          ∀ y : H, y ∈ C.carrier →
            inner Complex (E.operator i x) (E.operator j y) =
              scalar i j * inner Complex x y) ↔
      ∃ recovery : QuantumChannel H H,
        ∀ rho : DensityOperator H,
          DensityOperator.SupportedOn C rho →
            recovery (E.inducedMap rho.toOperator) = rho.toOperator := by sorry
