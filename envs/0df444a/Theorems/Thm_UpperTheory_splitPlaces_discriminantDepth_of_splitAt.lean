-- Prove2me | Theorems.Thm_UpperTheory_splitPlaces_discriminantDepth_of_splitAt
-- name    : UpperTheory.splitPlaces_discriminantDepth_of_splitAt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:30.784833+00:00
-- url     : https://prove2.me/theorems/a8a0cd06-21af-4c3b-b1e0-2fcdb07bca17
-- title:
--   Upper Theory: split Places discriminant Depth of split At
-- statement:
--   The Upper Theory construction uses the split Places discriminant Depth of split At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/SplitPlacesDiscriminantDepthOfSplitAt.lean#L59-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CMTraceForms/SplitPlacesDiscriminantDepthOfSplitAt.lean#L59-L149

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_Places
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsPrimitiveOrthogonalIdempotentsSumEqOfNoeth
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_ExistsSplitIdempotentOfSplitAt
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_TraceFormDecompositionCMDatum
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_DiscrCMDatumEqProdPlaces
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_SplitPlacesDiscriminantDepthOfSplitAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth
open UpperTheory.Depth.SplitPl

theorem UpperTheory.splitPlaces_discriminantDepth_of_splitAt :
    ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), SplitAt H.d p →
      ∀ f : ℕ, Module.finrank ℚ E = 2 * f → SplitPlaces p H f ((padicValInt p (NumberField.discr E) : ℝ) / (Module.finrank ℚ E : ℝ)) := by sorry
