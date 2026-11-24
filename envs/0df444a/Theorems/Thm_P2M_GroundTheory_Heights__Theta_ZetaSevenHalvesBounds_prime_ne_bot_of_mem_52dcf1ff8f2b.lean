-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_ne_bot_of_mem_52dcf1ff8f2b
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_ne_bot_of_mem_52dcf1ff8f2b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:58.436631+00:00
-- url     : https://prove2.me/theorems/1562036f-037d-40d2-9e7a-97a79d10a163
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prime ne bot of mem 52dcf1ff8f2b: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prime ne bot of mem 52dcf1ff8f2b
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prime ne bot of mem 52dcf1ff8f2b construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prime ne bot of mem 52dcf1ff8f2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L103-L106

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_ne_bot_of_mem_52dcf1ff8f2b {I P : Ideal (𝓞 K)} (h : P ∈ normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«prime_ne_bot_of_mem» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_ne_bot_of_mem_52dcf1ff8f2b
