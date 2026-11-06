-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_scale_complete_of_adjoint_square_sum
-- name    : QEC.Semantics.FiniteKrausFamily.scale_complete_of_adjoint_square_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:19:37.96549+00:00
-- url     : https://prove2.me/theorems/bdff82a5-a27d-45ca-a53f-297a9f073f34
-- title:
--   Finite Kraus Family: scale complete of adjoint square sum
-- statement:
--   Completeness of a scaled finite Kraus family from the corresponding weighted
--   adjoint-square sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L92-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L92-L111

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteKrausFamily.scale_complete_of_adjoint_square_sum
    (E : FiniteKrausFamily ι H K) (amp : ι → Complex)
    (h : ∑ i : ι, (star (amp i) * amp i) •
          ((LinearMap.adjoint (E.operator i)).comp (E.operator i)) = 1) :
    (E.scale amp).Complete := by sorry
