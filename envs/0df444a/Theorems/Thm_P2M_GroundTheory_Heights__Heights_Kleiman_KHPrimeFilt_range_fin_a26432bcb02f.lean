-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_range_fin_a26432bcb02f
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_range_fin_a26432bcb02f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:27:10.328132+00:00
-- url     : https://prove2.me/theorems/a0c420bc-885d-4df2-b89e-69cf0ac777d9
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt range fin a26432bcb02f: P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt range fin a26432bcb02f
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt range fin a26432bcb02f construction uses the P2 M Ground Theory Heights  Heights Kleiman KHPrime Filt range fin a26432bcb02f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L254-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHPrimeFilt.lean#L254-L261

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHPrimeFilt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.KHPrimeFilt

theorem P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_range_fin_a26432bcb02f {M : Type} {r : ℕ} (f : ℕ → M) :
    Set.range (fun l : Fin r => f l) = f '' {l : ℕ | l < r} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«KHPrimeFilt».«range_fin» := P2M_GroundTheory_Heights__Heights_Kleiman_KHPrimeFilt_range_fin_a26432bcb02f
