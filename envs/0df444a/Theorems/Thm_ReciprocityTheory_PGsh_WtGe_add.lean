-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_WtGe_add
-- name    : ReciprocityTheory.PGsh.WtGe.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:13.146899+00:00
-- url     : https://prove2.me/theorems/90c119bf-d395-4eaa-ab36-c361b6df5742
-- title:
--   Wt Ge: add
-- statement:
--   The Wt Ge construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WtGtRowSubstXSub.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WtGtRowSubstXSub.lean#L39-L43

import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
import Definitions.Def_ReciprocityTheory_DualLattices_WtGtRowSubstXSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}

theorem ReciprocityTheory.PGsh.WtGe.add {d : ℕ} {P Q : MvPolynomial (Fin ν × ι) ℂ} (h1 : WtGe d P) (h2 : WtGe d Q) :
    WtGe d (P + Q) := by sorry
