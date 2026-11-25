-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_embedC_eq_d6410787624d
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_embedC_eq_d6410787624d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:41:36.082989+00:00
-- url     : https://prove2.me/theorems/36166ea2-6963-423c-b9b2-fae449dd4341
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub exists embed C eq d6410787624d: P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub exists embed C eq d6410787624d
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub exists embed C eq d6410787624d construction uses the P2 M Ground Theory Heights  Heights Kleiman Fin Graded Sub exists embed C eq d6410787624d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L172-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTildeFinite.lean#L172-L191

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TildeFiniteSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechTransport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTildeFinite
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
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
variable (M : FinGradedSub (S := S) (x := x) Ω) (c : ℤ)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_embedC_eq_d6410787624d (n : ℕ) (w : Cech.Cochain (fun _ : StdCell N => ConeLaurent S x) n)
    (hw : w ∈ Cech.Cdeg (fun _ : StdCell N => ConeLaurent S x) (M.coneDeg c) n) :
    ∃ s, M.embedC c n s = w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«FinGradedSub».«exists_embedC_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_FinGradedSub_exists_embedC_eq_d6410787624d
