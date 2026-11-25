-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DehomogOrd_isPrime_map_C_2b9d3db6148a
-- name    : P2M_GroundTheory_Heights__Heights_DehomogOrd_isPrime_map_C_2b9d3db6148a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:42.672787+00:00
-- url     : https://prove2.me/theorems/49e93d6e-4dba-57bb-9dc9-85847ad3b427
-- title:
--   P2 M Ground Theory Heights  Heights Dehomog Ord is Prime map C 2b9d3db6148a: P2 M Ground Theory Heights  Heights Dehomog Ord is Prime map C 2b9d3db6148a
-- statement:
--   The P2 M Ground Theory Heights  Heights Dehomog Ord is Prime map C 2b9d3db6148a construction uses the P2 M Ground Theory Heights  Heights Dehomog Ord is Prime map C 2b9d3db6148a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PDehomogOrd.lean#L37-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PDehomogOrd
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
open GroundTheory.Heights₂.Heights.DehomogOrd

theorem P2M_GroundTheory_Heights__Heights_DehomogOrd_isPrime_map_C_2b9d3db6148a {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) [p.IsPrime] :
    (Ideal.map (C : R →+* MvPolynomial σ R) p).IsPrime := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DehomogOrd».«isPrime_map_C» := P2M_GroundTheory_Heights__Heights_DehomogOrd_isPrime_map_C_2b9d3db6148a
