-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prod_tuple_1b1f6df7d3f6
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prod_tuple_1b1f6df7d3f6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:00.646696+00:00
-- url     : https://prove2.me/theorems/8c9399dc-3597-5e6a-b0ea-dda763e7370d
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prod tuple 1b1f6df7d3f6: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prod tuple 1b1f6df7d3f6
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prod tuple 1b1f6df7d3f6 construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prod tuple 1b1f6df7d3f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L108-L114

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prod_tuple_1b1f6df7d3f6 {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : ∏ j, tuple K I j = absNorm I := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«prod_tuple» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prod_tuple_1b1f6df7d3f6
