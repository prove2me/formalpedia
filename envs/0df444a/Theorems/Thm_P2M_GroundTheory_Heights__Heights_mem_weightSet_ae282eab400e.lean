-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e
-- name    : P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:00.270083+00:00
-- url     : https://prove2.me/theorems/1fb3addc-d9a6-48fb-adda-2ebaf3b43fd9
-- title:
--   P2 M Ground Theory Heights  Heights mem weight Set ae282eab400e: P2 M Ground Theory Heights  Heights mem weight Set ae282eab400e
-- statement:
--   The P2 M Ground Theory Heights  Heights mem weight Set ae282eab400e construction uses the P2 M Ground Theory Heights  Heights mem weight Set ae282eab400e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L31-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
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
open MvPolynomial
noncomputable section
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}

theorem P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e {p : MvPolynomial σ R} {a : ℕ} :
    a ∈ weightSet w p ↔ ∃ d ∈ p.support, Finsupp.weight w d = a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_weightSet» := P2M_GroundTheory_Heights__Heights_mem_weightSet_ae282eab400e
