-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion
-- name    : QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:42:01.974094+00:00
-- url     : https://prove2.me/theorems/31cfc1dd-a83a-4ad1-a456-849735768ae7
-- title:
--   Finite Kraus Family: indexed Knill Laflamme Criterion iff same Space Knill Laflamme Criterion
-- statement:
--   The indexed same-space finite-Kraus KL criterion is equivalent to the existing
--   error-set criterion over `E.sameSpaceErrorSet`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L252-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L252-L261

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

theorem QEC.Semantics.FiniteKrausFamily.indexedKnillLaflammeCriterion_iff_sameSpaceKnillLaflammeCriterion
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) :
    IndexedKnillLaflammeCriterion E C ↔ E.sameSpaceKnillLaflammeCriterion C := by sorry
