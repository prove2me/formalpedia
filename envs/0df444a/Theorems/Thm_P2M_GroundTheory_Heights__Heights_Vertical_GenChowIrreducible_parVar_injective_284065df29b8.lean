-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_parVar_injective_284065df29b8
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_parVar_injective_284065df29b8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:17.13753+00:00
-- url     : https://prove2.me/theorems/de399fa9-801a-5352-adae-748f442552e9
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible par Var injective 284065df29b8: P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible par Var injective 284065df29b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible par Var injective 284065df29b8 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible par Var injective 284065df29b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean#L51-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenChowIrreducible
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
open GroundTheory.Heights₂.Heights.Vertical.GenChowIrreducible
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_parVar_injective_284065df29b8 : Function.Injective (parVar e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenChowIrreducible».«parVar_injective» := P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_parVar_injective_284065df29b8
