-- Prove2me | Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_exists_etaleChart_comap_subscheme__eraseIdx_fdb03de3c0d1
-- name    : P2M_FunctorialResolution_EmbeddedResolution_exists_etaleChart_comap_subscheme__eraseIdx_fdb03de3c0d1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:40.538464+00:00
-- url     : https://prove2.me/theorems/4bbf7fbc-3055-4877-9805-b33da6d87f2c
-- title:
--   P2 M Functorial Resolution Embedded Resolution exists etale Chart comap subscheme  erase Idx fdb03de3c0d1: P2 M Functorial Resolution Embedded Resolution exists etale Chart comap subscheme  erase Idx
-- statement:
--   The P2 M Functorial Resolution Embedded Resolution exists etale Chart comap subscheme  erase Idx fdb03de3c0d1 construction uses the P2 M Functorial Resolution Embedded Resolution exists etale Chart comap subscheme  erase Idx fdb03de3c0d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/StrictNormalCrossingsEraseMember.lean#L104-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/StrictNormalCrossingsEraseMember.lean#L104-L182

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_StrictNormalCrossingsEraseMember
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem P2M_FunctorialResolution_EmbeddedResolution_exists_etaleChart_comap_subscheme__eraseIdx_fdb03de3c0d1 {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E)
    (j : ℕ) (hj : j < E.length) (z : ↥((E[j]'hj).subscheme)) :
    ∃ (U : ((E[j]'hj).subscheme).Opens) (_ : z ∈ U) (m : ℕ)
      (c : EtaleChart ((E[j]'hj).subschemeι ≫ p) U m) (a : ℕ → Option (Fin m)),
      (∀ i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ i' < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length,
        ∀ t : Fin m, a i = some t → a i' = some t → i = i') ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length),
        a i = none →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < ((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι).length)
        (t : Fin m), a i = some t →
          restrictIdeal (((E.eraseIdx j).map fun D => D.comap (E[j]'hj).subschemeι)[i]) U =
            c.coordIdeal {t}) := by sorry

alias «FunctorialResolution».«EmbeddedResolution».«exists_etaleChart_comap_subschemeι_eraseIdx» := P2M_FunctorialResolution_EmbeddedResolution_exists_etaleChart_comap_subscheme__eraseIdx_fdb03de3c0d1
