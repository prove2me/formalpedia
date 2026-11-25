-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_label_inj_299e2bc1f903
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_label_inj_299e2bc1f903
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:26.59246+00:00
-- url     : https://prove2.me/theorems/79fc7a3f-c347-4e20-9c55-be73694f1ad4
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds label inj 299e2bc1f903: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds label inj 299e2bc1f903
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds label inj 299e2bc1f903 construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds label inj 299e2bc1f903 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L91-L95

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_label_inj_299e2bc1f903 {P Q : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : Q.IsPrime)
    (hQ0 : Q ≠ ⊥) (e : ratPrime K P = ratPrime K Q) (h : label K P = label K Q) : P = Q := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«label_inj» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_label_inj_299e2bc1f903
