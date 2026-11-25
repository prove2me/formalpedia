-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_sum_reindex_e19d84f6339c
-- name    : P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_sum_reindex_e19d84f6339c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:15:59.409361+00:00
-- url     : https://prove2.me/theorems/0dafe3ba-5c8f-488f-b727-2c7043c4b63a
-- title:
--   P2 M Ground Theory Heights  Heights Cauchy Binet Alt sum reindex e19d84f6339c: P2 M Ground Theory Heights  Heights Cauchy Binet Alt sum reindex e19d84f6339c
-- statement:
--   The P2 M Ground Theory Heights  Heights Cauchy Binet Alt sum reindex e19d84f6339c construction uses the P2 M Ground Theory Heights  Heights Cauchy Binet Alt sum reindex e19d84f6339c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCauchyBinet.lean#L42-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCauchyBinet.lean#L42-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Finset Equiv
open GroundTheory.Heights₂.Heights.CauchyBinetAlt
variable {R : Type*} [CommRing R] {j N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_sum_reindex_e19d84f6339c {M : Type*} [AddCommMonoid M] (g : (Fin j → Fin N) → M)
    (hg : ∀ p, ¬ Function.Injective p → g p = 0) :
    ∑ p, g p = ∑ I : {I : Finset (Fin N) // I.card = j}, ∑ w : Perm (Fin j),
      g (I.1.orderEmbOfFin I.2 ∘ w) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CauchyBinetAlt».«sum_reindex» := P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_sum_reindex_e19d84f6339c
