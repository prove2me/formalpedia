-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_dedekindZetaReal_le_pow_63af13c1180c
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_dedekindZetaReal_le_pow_63af13c1180c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:52:55.789638+00:00
-- url     : https://prove2.me/theorems/2e201004-9f10-4f66-a11e-013491b58f23
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds dedekind Zeta Real le pow 63af13c1180c: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds dedekind Zeta Real le pow 63af13c1180c
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds dedekind Zeta Real le pow 63af13c1180c construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds dedekind Zeta Real le pow 63af13c1180c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L211-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L211-L216

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_dedekindZetaReal_le_pow_63af13c1180c {s : ℝ} (hs : 1 < s) :
    GroundTheory.Global.dedekindZetaReal K s ≤ (∑' m : ℕ, (m : ℝ) ^ (-s)) ^ Module.finrank ℚ K := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«dedekindZetaReal_le_pow» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_dedekindZetaReal_le_pow_63af13c1180c
