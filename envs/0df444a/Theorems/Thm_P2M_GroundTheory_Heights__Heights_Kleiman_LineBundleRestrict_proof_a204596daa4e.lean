-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundleRestrict_proof_a204596daa4e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_LineBundleRestrict_proof_a204596daa4e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:09.669422+00:00
-- url     : https://prove2.me/theorems/e4df8323-84a8-5a3b-8640-dd1e36d90288
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Line Bundle Restrict proof a204596daa4e: P2 M Ground Theory Heights  Heights Kleiman Line Bundle Restrict proof a204596daa4e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Line Bundle Restrict proof a204596daa4e construction uses the P2 M Ground Theory Heights  Heights Kleiman Line Bundle Restrict proof a204596daa4e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L176-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PLineBundleRestrict.lean#L176-L186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LineBundleRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineBundleRestrict
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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {K' : Type w} [Field K']
  [Algebra k K'] {N : ℕ} {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'}
variable (hsp : primeOf (S := k) x ≤ primeOf (S := k) y) (hxy : ∀ i, y i ≠ 0 → x i ≠ 0)
include hsp
variable {γ : Ω} {Q : LineBundle k x}
omit hsp

theorem P2M_GroundTheory_Heights__Heights_Kleiman_LineBundleRestrict_proof_a204596daa4e : LineBundleRestrict.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«LineBundleRestrict».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_LineBundleRestrict_proof_a204596daa4e
