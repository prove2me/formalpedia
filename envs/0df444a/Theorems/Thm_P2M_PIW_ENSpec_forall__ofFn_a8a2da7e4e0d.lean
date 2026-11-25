-- Prove2me | Theorems.Thm_P2M_PIW_ENSpec_forall__ofFn_a8a2da7e4e0d
-- name    : P2M_PIW_ENSpec_forall__ofFn_a8a2da7e4e0d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:46.170845+00:00
-- url     : https://prove2.me/theorems/3b6ef3ce-dd0b-4e57-8675-22b6a1ca6f47
-- title:
--   P2 M PIW ENSpec forall  of Fn a8a2da7e4e0d: P2 M PIW ENSpec forall  of Fn a8a2da7e4e0d
-- statement:
--   The P2 M PIW ENSpec forall  of Fn a8a2da7e4e0d construction uses the P2 M PIW ENSpec forall  of Fn a8a2da7e4e0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L60-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottComplex/WregOfSubsingleton.lean#L60-L66

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_StSpecOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottComplex_WregOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open PIW PIW.ENSpec
open MvPolynomial RingTheory.Sequence
open scoped Pointwise
variable {S : Type u} [CommRing S]

theorem P2M_PIW_ENSpec_forall__ofFn_a8a2da7e4e0d {α β : Type*} {P : α → β → Prop} :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, P (f i) (g i)) →
      List.Forall₂ P (List.ofFn f) (List.ofFn g)
  := by sorry

alias «PIW».«ENSpec».«forall₂_ofFn» := P2M_PIW_ENSpec_forall__ofFn_a8a2da7e4e0d
