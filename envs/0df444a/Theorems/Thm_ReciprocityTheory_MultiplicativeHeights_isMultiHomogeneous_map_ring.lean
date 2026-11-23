-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_isMultiHomogeneous_map_ring
-- name    : ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:13.950807+00:00
-- url     : https://prove2.me/theorems/8b6f26e2-c4c9-4243-8b90-d70149c969e4
-- title:
--   Multiplicative Heights: is Multi Homogeneous map ring
-- statement:
--   The Multiplicative Heights construction uses the is Multi Homogeneous map ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LagrangeIdealLiftsFact.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LagrangeIdealLiftsFact.lean#L29-L39

import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_LagrangeIdealLiftsFact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory NumberField

theorem ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring {K : Type*} [Field K] {B n : ℕ} (a : Fin B → ℕ)
    (f : MvPolynomial (Fin B × Fin n) K) (hf : IsMultiHomogeneous a f) (φ : K →+* ℂ) :
    IsMultiHomogeneous a (MvPolynomial.map φ f) := by sorry
