-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedProjectorConditionWithScalar_adjoint_projector
-- name    : QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_adjoint_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:44:31.128273+00:00
-- url     : https://prove2.me/theorems/76b8f394-397d-4b96-a66d-fd3d837cfa5e
-- title:
--   Finite Kraus Family: indexed Projector Condition With Scalar adjoint projector
-- statement:
--   Indexed KL projector data is Hermitian on the code projector.  The equality is
--   kept at projector level so it remains valid for degenerate code carriers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L67-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/KLRecovery.lean#L67-L99

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

theorem QEC.Semantics.FiniteKrausFamily.indexedProjectorConditionWithScalar_adjoint_projector
    {E : FiniteKrausFamily ι H H} {C : QuantumCode H}
    {scalar : ι → ι → Complex}
    (hKL : IndexedKnillLaflammeProjectorConditionWithScalar E C scalar)
    (i j : ι) :
    star (scalar i j) • C.projector = scalar j i • C.projector := by sorry
