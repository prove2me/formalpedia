-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_factorization_tuple_da2abc16b590
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_factorization_tuple_da2abc16b590
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:21.1446+00:00
-- url     : https://prove2.me/theorems/d1ed12c3-43d8-4010-a8e3-a37a46346872
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds factorization tuple da2abc16b590: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds factorization tuple da2abc16b590
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds factorization tuple da2abc16b590 construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds factorization tuple da2abc16b590 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L116-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L116-L147

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_factorization_tuple_da2abc16b590 (I : Ideal (𝓞 K)) {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (tuple K I (label K P)).factorization (ratPrime K P) =
      (normalizedFactors I).count P * (absNorm P).factorization (ratPrime K P) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«factorization_tuple» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_factorization_tuple_da2abc16b590
