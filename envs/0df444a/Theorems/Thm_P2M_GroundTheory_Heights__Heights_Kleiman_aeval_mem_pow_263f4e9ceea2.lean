-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_pow_263f4e9ceea2
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_pow_263f4e9ceea2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:38.853634+00:00
-- url     : https://prove2.me/theorems/1bee36ed-1ebb-492a-bf95-d24ba01af3d6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman aeval mem pow 263f4e9ceea2: P2 M Ground Theory Heights  Heights Kleiman aeval mem pow 263f4e9ceea2
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman aeval mem pow 263f4e9ceea2 construction uses the P2 M Ground Theory Heights  Heights Kleiman aeval mem pow 263f4e9ceea2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L31-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSectionCountTop.lean#L31-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SectionCountTopSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSectionCountTop
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_pow_263f4e9ceea2 (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (I : Chart x) {f : MvPolynomial (Fin (r + 1)) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    aeval h f ∈ (Q.pow n).sub I := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«aeval_mem_pow» := P2M_GroundTheory_Heights__Heights_Kleiman_aeval_mem_pow_263f4e9ceea2
