-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_RankOneLeviIdentities_reflection_apply_entries
-- name    : ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.reflection_apply_entries
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:53:39.967193+00:00
-- url     : https://prove2.me/theorems/c3ac5bc5-aec5-4a1d-9944-3779f06707f6
-- title:
--   Rank One Levi Identities: reflection apply entries
-- statement:
--   The Rank One Levi Identities construction uses the reflection apply entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L205-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/HermitianFormBaseVectorRight.lean#L205-L208

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormBaseVectorRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k r' : ℕ)

theorem ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities.reflection_apply_entries (c : ℂ) (p q : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c p q = if p.val = 0 ∧ q.val = 2 * (1 + r') + k then (star c)⁻¹
      else if p.val = 2 * (1 + r') + k ∧ q.val = 0 then c
      else if p = q ∧ 0 < p.val ∧ p.val < 2 * (1 + r') + k then 1 else 0 := by sorry
