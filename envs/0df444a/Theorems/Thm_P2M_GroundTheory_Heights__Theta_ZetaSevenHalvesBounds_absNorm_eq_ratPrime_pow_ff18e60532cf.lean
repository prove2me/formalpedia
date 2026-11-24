-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_absNorm_eq_ratPrime_pow_ff18e60532cf
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_absNorm_eq_ratPrime_pow_ff18e60532cf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:03.893176+00:00
-- url     : https://prove2.me/theorems/832304c4-7db3-410e-873e-d7781ccc0b83
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds abs Norm eq rat Prime pow ff18e60532cf: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds abs Norm eq rat Prime pow ff18e60532cf
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds abs Norm eq rat Prime pow ff18e60532cf construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds abs Norm eq rat Prime pow ff18e60532cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L30-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L30-L43

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_absNorm_eq_ratPrime_pow_ff18e60532cf {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    absNorm P = ratPrime K P ^ (absNorm P).factorization (ratPrime K P) ∧
      0 < (absNorm P).factorization (ratPrime K P) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«absNorm_eq_ratPrime_pow» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_absNorm_eq_ratPrime_pow_ff18e60532cf
