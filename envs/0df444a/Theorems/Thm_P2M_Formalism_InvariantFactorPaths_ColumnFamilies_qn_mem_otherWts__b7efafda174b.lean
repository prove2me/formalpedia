-- Prove2me | Theorems.Thm_P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_otherWts__b7efafda174b
-- name    : P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_otherWts__b7efafda174b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:45.859821+00:00
-- url     : https://prove2.me/theorems/4b97587f-3317-4027-bc70-deae86cf631a
-- title:
--   P2 M Formalism Invariant Factor Paths Column Families qn mem other Wts  b7efafda174b: P2 M Formalism Invariant Factor Paths Column Families qn mem other Wts  b7efafda174b
-- statement:
--   The P2 M Formalism Invariant Factor Paths Column Families qn mem other Wts  b7efafda174b construction uses the P2 M Formalism Invariant Factor Paths Column Families qn mem other Wts  b7efafda174b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L95-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/CoeffTransposeVariables.lean#L95-L109

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TransposeVariables
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility

theorem P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_otherWts__b7efafda174b (n : ℕ) (ν : Fin n → ℕ) (g : MvPolynomial (Fin n × Fin n) ℚ)
    (hg : weightedHomogeneousComponent (rowW n n) ν (transposeVariables ℚ n g) = 0) :
    g ∈ otherWts (glOps ℚ n (rowLetters n) Set.univ) (fun a => (ν a : ℤ)) := by sorry

alias «Formalism».«InvariantFactorPaths».«ColumnFamilies».«qn_mem_otherWts'» := P2M_Formalism_InvariantFactorPaths_ColumnFamilies_qn_mem_otherWts__b7efafda174b
