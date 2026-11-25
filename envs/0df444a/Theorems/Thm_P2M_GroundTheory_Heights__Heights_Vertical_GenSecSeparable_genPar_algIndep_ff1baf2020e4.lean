-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_genPar_algIndep_ff1baf2020e4
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_genPar_algIndep_ff1baf2020e4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:42:20.565982+00:00
-- url     : https://prove2.me/theorems/14976328-82fc-4bff-9a5a-9040cc5b22f4
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable gen Par alg Indep ff1baf2020e4: P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable gen Par alg Indep ff1baf2020e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable gen Par alg Indep ff1baf2020e4 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Sec Separable gen Par alg Indep ff1baf2020e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenSecSeparable.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChartPointTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsSecPointSeparable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecSeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.GenSecSeparable

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_genPar_algIndep_ff1baf2020e4 (k : Type*) [Field k] (e n : ℕ) :
    AlgebraicIndependent k (genPar k e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenSecSeparable».«genPar_algIndep» := P2M_GroundTheory_Heights__Heights_Vertical_GenSecSeparable_genPar_algIndep_ff1baf2020e4
