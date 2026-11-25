-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tpow_1e634deba6a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tpow_1e634deba6a8
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:34:16.605178+00:00
-- url     : https://prove2.me/theorems/331cb355-6084-40b3-8897-2218fca132c2
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman bundle Num tpow 1e634deba6a8: P2 M Ground Theory Heights  Heights Kleiman bundle Num tpow 1e634deba6a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman bundle Num tpow 1e634deba6a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman bundle Num tpow 1e634deba6a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L159-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PNefProductNonneg.lean#L159-L167

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistBundleToSubSystem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefProductNonneg
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
  {x : Fin (N + 1) → Ω}
variable (hR : GenericPointSectionInput.Statement.{u, w})
include hR

theorem P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tpow_1e634deba6a8 {pp : Ideal (Poly k N)} {n : ℕ} (hW : IsSubvar x pp n)
    (L : Fin n → LineBundle k x) (i : Fin n) (M : LineBundle k x) (p : ℕ) :
    bundleNum pp (Function.update L i (M.tpow p)) = p * bundleNum pp (Function.update L i M) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«bundleNum_tpow» := P2M_GroundTheory_Heights__Heights_Kleiman_bundleNum_tpow_1e634deba6a8
