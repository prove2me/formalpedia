-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_XI_gN_nonneg
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.XI.gN_nonneg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:52:35.982896+00:00
-- url     : https://prove2.me/theorems/2b09fd07-ce10-5917-a14c-1bc84059078f
-- title:
--   XI: g N nonneg
-- statement:
--   The XI construction uses the g N nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaNonneg.lean#L111-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GaNonneg.lean#L111-L111

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GaNonneg
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
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.XI
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS ReciprocityTheory.ChartRestriction.DS.Xi.GSB

theorem ReciprocityTheory.ChartRestriction.DS.Xi.XI.gN_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ gN g := by sorry
