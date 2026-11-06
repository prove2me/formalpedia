-- Prove2me | Theorems.Thm_QEC_Semantics_clbtGeneratorBlockThree_bound
-- name    : QEC.Semantics.clbtGeneratorBlockThree_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:01.268899+00:00
-- url     : https://prove2.me/theorems/631e7533-f92d-4769-9506-ef1e99ace958
-- title:
--   Semantics: clbt Generator Block Three bound
-- statement:
--   Each CLBT block has the common source-local upper bound; block three.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L556-L591
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/FourBlockGenerator.lean#L556-L591

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]

theorem QEC.Semantics.clbtGeneratorBlockThree_bound [Fintype ι] [Nontrivial H]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hO : O.IsSymmetric) (hP : IsStarProjection P)
    (hOP : Commute O P) (hOrho : Commute O rho.toOperator)
    (hPrho : Commute P rho.toOperator) (hOnorm : operatorNorm O ≤ 2) :
    traceNorm
        (clbtGeneratorBlockThree (lindbladDissipator J) O P rho.toOperator) ≤
      2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by sorry
