-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_OswLocFin_measurePreserving_of_addEquiv
-- name    : PositivityTheory.SiegelWeilFormula.OswLocFin.measurePreserving_of_addEquiv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:56:56.043675+00:00
-- url     : https://prove2.me/theorems/f1ddf6a8-ea90-5d95-988a-20a69390cc01
-- title:
--   Osw Loc Fin: measure Preserving of add Equiv
-- statement:
--   The Osw Loc Fin construction uses the measure Preserving of add Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalInvariantNeighborhoods/MeasurePreservingOfAddEquiv.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalInvariantNeighborhoods/MeasurePreservingOfAddEquiv.lean#L7-L27

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalInvariantNeighborhoods_MeasurePreservingOfAddEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.OswLocFin
open MeasureTheory

theorem PositivityTheory.SiegelWeilFormula.OswLocFin.measurePreserving_of_addEquiv {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    (e : G ≃+ G) (he : Continuous e) (he' : Continuous e.symm) (B : Set G) (hB : IsCompact B)
    (hB' : (interior B).Nonempty) (heB : e ⁻¹' B = B) :
    MeasureTheory.MeasurePreserving e μ μ := by sorry
