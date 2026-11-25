-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_summable_dedekindZetaTerm_6d837e00dbf1
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_summable_dedekindZetaTerm_6d837e00dbf1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:35.934846+00:00
-- url     : https://prove2.me/theorems/b0a99649-b3f7-4f88-a33c-449bcc32af5c
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds summable dedekind Zeta Term 6d837e00dbf1: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds summable dedekind Zeta Term 6d837e00dbf1
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds summable dedekind Zeta Term 6d837e00dbf1 construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds summable dedekind Zeta Term 6d837e00dbf1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L219-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L219-L224

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_ZetaSevenHalves
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid
noncomputable section
open GroundTheory.Heights₂.Theta.ZetaSevenHalvesBounds
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_summable_dedekindZetaTerm_6d837e00dbf1 {s : ℝ} (hs : 1 < s) :
    Summable (GroundTheory.Global.dedekindZetaTerm K s) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«summable_dedekindZetaTerm» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_summable_dedekindZetaTerm_6d837e00dbf1
