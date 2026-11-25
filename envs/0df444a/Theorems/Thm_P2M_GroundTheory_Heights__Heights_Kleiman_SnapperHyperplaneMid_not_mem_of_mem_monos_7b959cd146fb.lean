-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_not_mem_of_mem_monos_7b959cd146fb
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_not_mem_of_mem_monos_7b959cd146fb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:22.472462+00:00
-- url     : https://prove2.me/theorems/c4393dd9-82a3-5fe0-9600-1150ccaad484
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid not mem of mem monos 7b959cd146fb: P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid not mem of mem monos 7b959cd146
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid not mem of mem monos 7b959cd146fb construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Hyperplane Mid not mem of mem monos 7b959cd146fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperHyperplaneMid.lean#L65-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDevissage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperHyperplaneMid
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
open GroundTheory.Heights₂.Heights.Kleiman.SnapperHyperplaneMid
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_not_mem_of_mem_monos_7b959cd146fb {pp : Ideal (Poly k N)} (hp : pp.IsPrime) {I : Finset (Fin (N + 1))}
    (hI : ∀ l ∈ I, (X l : Poly k N) ∉ pp) {s : Poly k N} (hs : s ∈ monos I) : s ∉ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperHyperplaneMid».«not_mem_of_mem_monos» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperHyperplaneMid_not_mem_of_mem_monos_7b959cd146fb
