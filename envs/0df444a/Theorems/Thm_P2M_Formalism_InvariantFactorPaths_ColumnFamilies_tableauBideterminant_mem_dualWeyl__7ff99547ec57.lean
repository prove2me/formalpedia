-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_mem_dualWeyl__7ff99547ec57
-- name    : P2M_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_mem_dualWeyl__7ff99547ec57
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:26.45095+00:00
-- url     : https://prove2.me/theorems/6cbcde71-106c-4552-8d19-706399bcb0c3
-- title:
--   P2 M Formalism Invariant Factor Paths Column Families tableau Bideterminant mem dual Weyl  7ff99547ec57: P2 M Formalism Invariant Factor Paths Column Families tableau Bideterminant mem dual Weyl  7ff9
-- statement:
--   The P2 M Formalism Invariant Factor Paths Column Families tableau Bideterminant mem dual Weyl  7ff99547ec57 construction uses the P2 M Formalism Invariant Factor Paths Column Families tableau Bideterminant mem dual Weyl  7ff99547ec57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/EqSmulCanonicalOfUnipotentInvariant.lean#L110-L111

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]

theorem P2M_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_mem_dualWeyl__7ff99547ec57 (mu : Fin n → ℤ) (I : TIdx mu) : qd_P mu I ∈ dualWeyl ℚ n n (qd_nu mu) := by sorry

alias «Formalism».«InvariantFactorPaths».«ColumnFamilies».«tableauBideterminant_mem_dualWeyl'» := P2M_Formalism_InvariantFactorPaths_ColumnFamilies_tableauBideterminant_mem_dualWeyl__7ff99547ec57
