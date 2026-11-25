-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_4c00e12af7e2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_4c00e12af7e2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:59.901093+00:00
-- url     : https://prove2.me/theorems/62fcaf5a-4fac-4fa9-beda-5a5ffd719cf6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sign swap 4c00e12af7e2: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sign swap 4c00e1
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sign swap 4c00e12af7e2 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Cell DSq sign swap 4c00e12af7e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L103-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DoubleSumEqZero.lean#L103-L119

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_4c00e12af7e2 {I : ∀ k, Finset (ι k)} {p q : Σ k, ι k} (hp : p.2 ∈ I p.1) (hq : q.2 ∈ I q.1)
    (hne : q ≠ p) (hJ : ∀ l, (rem (rem I p) q l).Nonempty) :
    faceSign I p.1 p.2 * faceSign (rem I p) q.1 q.2 =
      -(faceSign I q.1 q.2 * faceSign (rem I q) p.1 p.2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«CellDSq».«sign_swap» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_sign_swap_4c00e12af7e2
