-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isMultiHomogeneous_iff_forall_weighted_lh0BlockWt
-- name    : ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_iff_forall_weighted_lh0BlockWt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:28:03.803668+00:00
-- url     : https://prove2.me/theorems/2bdf7449-602e-5362-b42d-903fafad1373
-- title:
--   Multiplicative Heights: is Multi Homogeneous iff forall weighted lh0 Block Wt
-- statement:
--   The Multiplicative Heights construction uses the is Multi Homogeneous iff forall weighted lh0 Block Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AevalIsWeightedHomogeneous.lean#L19-L27

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AevalIsWeightedHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_iff_forall_weighted_lh0BlockWt {R : Type*} [CommSemiring R] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) R) :
    IsMultiHomogeneous a f ↔ ∀ b, IsWeightedHomogeneous (blockIndexWeight b) f (a b) := by sorry
