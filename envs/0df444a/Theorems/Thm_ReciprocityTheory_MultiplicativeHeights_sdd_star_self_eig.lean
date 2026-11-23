-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_star_self_eig
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_star_self_eig
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:30.542439+00:00
-- url     : https://prove2.me/theorems/b5a164a5-e8f3-4be3-8494-e5659a18239f
-- title:
--   Multiplicative Heights: sdd star self eig
-- statement:
--   The Multiplicative Heights construction uses the sdd star self eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L26-L33

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA
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
open Matrix NumberField
open scoped ComplexOrder MatrixOrder

theorem ReciprocityTheory.MultiplicativeHeights.sdd_star_self_eig {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (⇑(hD.eigenvectorBasis i)) = 1 := by sorry
