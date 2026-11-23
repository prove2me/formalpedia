-- Prove2me | Theorems.Thm_P2M_GroundTheory_Global_mixedTraceForm_apply__be78fc251b6f
-- name    : P2M_GroundTheory_Global_mixedTraceForm_apply__be78fc251b6f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:08:55.349799+00:00
-- url     : https://prove2.me/theorems/d663d644-7862-4446-baef-d6bc503742f9
-- title:
--   P2 M Ground Theory Global mixed Trace Form apply  be78fc251b6f: P2 M Ground Theory Global mixed Trace Form apply  be78fc251b6f
-- statement:
--   The P2 M Ground Theory Global mixed Trace Form apply  be78fc251b6f construction uses the P2 M Ground Theory Global mixed Trace Form apply  be78fc251b6f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TracePairing.lean#L63-L64

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem P2M_GroundTheory_Global_mixedTraceForm_apply__be78fc251b6f (x y : mixedSpace K) :
    mixedTraceForm K x y = ∑ w, x.1 w * y.1 w + ∑ w, 2 * (x.2 w * y.2 w).re := by sorry

alias «GroundTheory».«Global».«mixedTraceForm_apply'» := P2M_GroundTheory_Global_mixedTraceForm_apply__be78fc251b6f
