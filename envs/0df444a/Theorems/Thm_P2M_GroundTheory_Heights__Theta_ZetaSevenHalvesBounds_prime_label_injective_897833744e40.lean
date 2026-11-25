-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_label_injective_897833744e40
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_label_injective_897833744e40
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:08.072014+00:00
-- url     : https://prove2.me/theorems/abf252be-17e7-48e5-a87c-7dd76da363e6
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prime label injective 897833744e40: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prime label injective 897833744e40
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prime label injective 897833744e40 construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds prime label injective 897833744e40 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L68-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L68-L79

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_label_injective_897833744e40 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : p = q) {P Q : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))
    (hQ : Q ∈ primesOver (Ideal.span {(q : ℤ)}) (𝓞 K))
    (h : primeLabel K p hp P hP = primeLabel K q hq Q hQ) : P = Q := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«prime_label_injective» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_label_injective_897833744e40
