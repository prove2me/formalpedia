-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_specRest_X_7e3344781ad6
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_specRest_X_7e3344781ad6
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:24.077424+00:00
-- url     : https://prove2.me/theorems/e071bc82-6482-5172-9582-8e53503de593
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible spec Rest X 7e3344781ad6: P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible spec Rest X 7e3344781ad6
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible spec Rest X 7e3344781ad6 construction uses the P2 M Ground Theory Heights  Heights Vertical Gen Chow Irreducible spec Rest X 7e3344781ad6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGenChowIrreducible.lean#L55-L66

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_specRest_X_7e3344781ad6 {k : Type*} [Field k] (f : MvPolynomial (Fin (e + 1) × Fin n) k) :
    specRest (algebraMap k (MvPolynomial (Par e n) k)) f X =
      sumAlgEquiv k (Fin n) (Par e n) (rename (parVar e n) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«GenChowIrreducible».«specRest_X» := P2M_GroundTheory_Heights__Heights_Vertical_GenChowIrreducible_specRest_X_7e3344781ad6
