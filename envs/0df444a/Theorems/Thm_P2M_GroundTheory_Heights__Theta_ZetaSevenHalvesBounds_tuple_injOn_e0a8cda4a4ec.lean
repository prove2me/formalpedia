-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_tuple_injOn_e0a8cda4a4ec
-- name    : P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_tuple_injOn_e0a8cda4a4ec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:02.313415+00:00
-- url     : https://prove2.me/theorems/8ecc533e-0888-42da-b46a-03184eac9db9
-- title:
--   P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds tuple inj On e0a8cda4a4ec: P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds tuple inj On e0a8cda4a4ec
-- statement:
--   The P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds tuple inj On e0a8cda4a4ec construction uses the P2 M Ground Theory Heights  Theta Zeta Seven Halves Bounds tuple inj On e0a8cda4a4ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L149-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/DedekindZetaSeries/SummableDedekindZetaTerm.lean#L149-L163

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

theorem P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_tuple_injOn_e0a8cda4a4ec : Set.InjOn (tuple K) {I | I ≠ ⊥} := by sorry

alias «GroundTheory».«Heights₂».«Theta».«ZetaSevenHalvesBounds».«tuple_injOn» := P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_tuple_injOn_e0a8cda4a4ec
