-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_coeff_mul_term
-- name    : ReciprocityTheory.ChartRestriction.L1.coeff_mul_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:54.496398+00:00
-- url     : https://prove2.me/theorems/859ec05a-098a-48c9-8cd1-91aaddc1a1af
-- title:
--   L1: coeff mul term
-- statement:
--   The L1 construction uses the coeff mul term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModEvalSer.lean#L56-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffRescaleExpandOfNotDvd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModEvalSer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.coeff_mul_term (f g : PowerSeries ℂ) (x : ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) * x ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 f * x ^ kl.1) * (PowerSeries.coeff kl.2 g * x ^ kl.2) := by sorry
