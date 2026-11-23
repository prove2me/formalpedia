-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_quad_eig
-- name    : ReciprocityTheory.MultiplicativeHeights.sdd_quad_eig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:49.759211+00:00
-- url     : https://prove2.me/theorems/7612eb67-5902-47ef-b98a-7d2e523ec5f9
-- title:
--   Multiplicative Heights: sdd quad eig
-- statement:
--   The Multiplicative Heights construction uses the sdd quad eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SemiDegDA.lean#L35-L38

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

theorem ReciprocityTheory.MultiplicativeHeights.sdd_quad_eig {n : ℕ} {D : Matrix (Fin n) (Fin n) ℂ} (hD : D.IsHermitian) (i : Fin n) :
    star (⇑(hD.eigenvectorBasis i)) ⬝ᵥ (D *ᵥ ⇑(hD.eigenvectorBasis i)) = (hD.eigenvalues i : ℂ) := by sorry
