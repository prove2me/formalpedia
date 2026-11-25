-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_zetaSevenHalves_eq_tsum_288e87001abd
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_zetaSevenHalves_eq_tsum_288e87001abd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:35.407787+00:00
-- url     : https://prove2.me/theorems/96d13b78-8119-4175-a51f-750c6563fd8e
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds zeta Seven Halves eq tsum 288e87001abd: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds zeta Seven Halves eq tsum 288e87001abd
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds zeta Seven Halves eq tsum 288e87001abd construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds zeta Seven Halves eq tsum 288e87001abd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L226-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L226-L237

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_zetaSevenHalves_eq_tsum_288e87001abd :
    zetaSevenHalves = ∑' m : ℕ, (m : ℝ) ^ (-(7 / 2 : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«zetaSevenHalves_eq_tsum» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_zetaSevenHalves_eq_tsum_288e87001abd
