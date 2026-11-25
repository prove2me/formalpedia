-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_iic_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.iic_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:15.287989+00:00
-- url     : https://prove2.me/theorems/0a6c6f3c-1f86-5f7b-b239-058290e8100f
-- title:
--   Hermitian Lift Identities: iic eq
-- statement:
--   The Hermitian Lift Identities construction uses the iic eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/XphiLinInd.lean#L15-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_XphiLinInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities.iic_eq (l : Fin (r + 1)) :
    Finset.Iic l = Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)) := by sorry
