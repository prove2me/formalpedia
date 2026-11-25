-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interNumPoint_restrLen_eq_finrank_3e09ba07e8c2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_interNumPoint_restrLen_eq_finrank_3e09ba07e8c2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:00:40.0497+00:00
-- url     : https://prove2.me/theorems/96cb63be-0bbc-4e91-8c10-a61a5d2d7fb6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman inter Num Point restr Len eq finrank 3e09ba07e8c2: P2 M Ground Theory Heights  Heights Kleiman inter Num Point restr Len eq finrank 3e09ba07e8c2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman inter Num Point restr Len eq finrank 3e09ba07e8c2 construction uses the P2 M Ground Theory Heights  Heights Kleiman inter Num Point restr Len eq finrank 3e09ba07e8c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumPoint.lean#L17-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PInterNumPoint.lean#L17-L39

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_interNumPoint_restrLen_eq_finrank_3e09ba07e8c2 (y : Fin (N + 1) → Ω) {j : Fin (N + 1)} (hyj : y j ≠ 0)
    (F : SubSystem k y Ω) : restrLen (primeOf (S := k) y) F = Module.finrank k F.secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«interNumPoint_restrLen_eq_finrank» := P2M_GroundTheory_Heights__Heights_Kleiman_interNumPoint_restrLen_eq_finrank_3e09ba07e8c2
