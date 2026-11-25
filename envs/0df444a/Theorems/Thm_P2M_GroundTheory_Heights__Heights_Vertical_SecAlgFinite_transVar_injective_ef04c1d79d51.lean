-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_transVar_injective_ef04c1d79d51
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_transVar_injective_ef04c1d79d51
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:36.864621+00:00
-- url     : https://prove2.me/theorems/012833ba-9236-4830-b11c-6c94ecee626a
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Alg Finite trans Var injective ef04c1d79d51: P2 M Ground Theory Heights  Heights Vertical Sec Alg Finite trans Var injective ef04c1d79d51
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Alg Finite trans Var injective ef04c1d79d51 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Alg Finite trans Var injective ef04c1d79d51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFinite.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFinite.lean#L28-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFinite
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
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFinite
variable {k E : Type} [Field k] [Field E] [Algebra k E] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_transVar_injective_ef04c1d79d51 (m : Fin n) :
    Function.Injective (aeval (R := k) (transVar (k := k) (e := e) m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecAlgFinite».«transVar_injective» := P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFinite_transVar_injective_ef04c1d79d51
