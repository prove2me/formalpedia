-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_FactorConjugationCancel_map_eq_of_conj
-- name    : UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:39:41.611448+00:00
-- url     : https://prove2.me/theorems/34b1a639-33e9-4064-99b3-8d6960b04397
-- title:
--   Factor Conjugation Cancel: map eq of conj
-- statement:
--   The Factor Conjugation Cancel construction uses the map eq of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FactorConjugationCancel.lean#L24-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FactorConjugationCancel.lean#L24-L58

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FactorConjugationCancel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory

theorem UpperTheory.Reformulated.B.FactorConjugationCancel.map_eq_of_conj :
    ∀ {G : Type} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [inst_5 : MeasurableSpace G]
    [BorelSpace G] (m s : G ≃ₜ+ G) (ν : MeasureTheory.Measure G) [ν.IsAddHaarMeasure] (c : NNReal),
    (∀ (x : G), (s : G → G) ((s : G → G) x) = x) →
      MeasureTheory.Measure.map (fun (x : G) ↦ (s : G → G) ((m : G → G) ((s : G → G) ((m : G → G) x)))) ν = (c * c) • ν →
        MeasureTheory.Measure.map (⇑m : G → G) ν = c • ν := by sorry
