-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_restrLen_of_irrelevant_97ff5d9d626a
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_restrLen_of_irrelevant_97ff5d9d626a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:02:41.940479+00:00
-- url     : https://prove2.me/theorems/b87612b6-ed71-4097-9fd8-6465df567a7a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman restr Len of irrelevant 97ff5d9d626a: P2 M Ground Theory Heights  Heights Kleiman restr Len of irrelevant 97ff5d9d626a
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman restr Len of irrelevant 97ff5d9d626a construction uses the P2 M Ground Theory Heights  Heights Kleiman restr Len of irrelevant 97ff5d9d626a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L30-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCycleSplit.lean#L30-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCycleSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_restrLen_of_irrelevant_97ff5d9d626a (pp : Ideal (Poly S N)) (hX : ∀ i, (X i : Poly S N) ∈ pp)
    (F : SubSystem S x Ω) : restrLen pp F = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«restrLen_of_irrelevant» := P2M_GroundTheory_Heights__Heights_Kleiman_restrLen_of_irrelevant_97ff5d9d626a
