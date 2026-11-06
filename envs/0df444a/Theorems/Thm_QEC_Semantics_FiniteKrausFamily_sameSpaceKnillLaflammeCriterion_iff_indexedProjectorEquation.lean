-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation
-- name    : QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:44:41.453407+00:00
-- url     : https://prove2.me/theorems/42008222-5cbc-4acd-bff5-8a211c1e3203
-- title:
--   Finite Kraus Family: same Space Knill Laflamme Criterion iff indexed Projector Equation
-- statement:
--   The same-space finite-Kraus KL criterion is equivalent to projector equations
--   with scalars indexed by the original Kraus family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L297-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L297-L302

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.sameSpaceKnillLaflammeCriterion_iff_indexedProjectorEquation
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    E.sameSpaceKnillLaflammeCriterion C ↔
      IndexedKnillLaflammeProjectorEquation E C := by sorry
