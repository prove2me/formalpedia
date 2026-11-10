-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fullCenterQuery_value
-- name    : QEC.Coding.BDL26RandomPerturbation.fullCenterQuery_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T03:16:23.516971+00:00
-- url     : https://prove2.me/theorems/37c81d6b-a94d-4ed1-bdbd-1ce761134d4e
-- title:
--   BDL26 Random Perturbation: full Center Query value
-- statement:
--   The BDL26 Random Perturbation construction uses the full Center Query value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean#L19-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FullEventQuery.lean#L19-L25

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_AnchorQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridEnumerationQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SnapshotQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FullEventQuery
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.fullCenterQuery_value (P : TannerSquarePresentation) (J : Vertex P → Space)
    (r lambda : ℝ) (K : ℕ) (e : Event P J r) (g : Grid K) :
    (fullCenterQuery P J lambda K (eventAnchorQuery P J r e).1 g).1 =
      eventCenter P J r lambda K e g := by sorry
