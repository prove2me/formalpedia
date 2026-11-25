-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_ell_lev
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.BL.ell_lev
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:04:26.872458+00:00
-- url     : https://prove2.me/theorems/eba1cecd-5424-54da-95b9-48beef0d3f09
-- title:
--   BL: ell lev
-- statement:
--   The BL construction uses the ell lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormLiftVecFirstVector.lean#L225-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormLiftVecFirstVector.lean#L225-L241

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Xi.BL.ell_lev (hHA : HeisAct) (z1 : Fin (2 * r' + k + 1) → ℂ) (m : Mat k r') (X : HPar k r') :
    ell k (1 + r') (liftVec k 1 r' z1) (heis0 k r' X * ιLev k 1 r' m) =
      -herm (Hpk k r') (m *ᵥ fvec k r' z1 ⟨0, by omega⟩) X.1 + ell k r' z1 m := by sorry
