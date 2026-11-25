-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interNumPoint_interSum_eq_21399a25c2ce
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_interNumPoint_interSum_eq_21399a25c2ce
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:04:12.270834+00:00
-- url     : https://prove2.me/theorems/41c7e8fd-09e1-5a64-b269-f151e00fe3ab
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman inter Num Point inter Sum eq 21399a25c2ce: P2 M Ground Theory Heights  Heights Kleiman inter Num Point inter Sum eq 21399a25c2ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman inter Num Point inter Sum eq 21399a25c2ce construction uses the P2 M Ground Theory Heights  Heights Kleiman inter Num Point inter Sum eq 21399a25c2ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumPoint.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumPoint.lean#L41-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_InterNumPointSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PInterNumPoint
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
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_interNumPoint_interSum_eq_21399a25c2ce (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (L : Fin 0 → SubSystem k y Ω) (c : ℕ) :
    interSum (primeOf (S := k) y) L c = Module.finrank k (twistSys k y (c : ℤ)).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«interNumPoint_interSum_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_interNumPoint_interSum_eq_21399a25c2ce
