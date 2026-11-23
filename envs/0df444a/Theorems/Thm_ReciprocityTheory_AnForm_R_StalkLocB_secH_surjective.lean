-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_StalkLocB_secH_surjective
-- name    : ReciprocityTheory.AnForm.R.StalkLocB.secH_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:01:47.656474+00:00
-- url     : https://prove2.me/theorems/62f3bc5c-312e-472d-a6d6-3a8ed0c95c7d
-- title:
--   Stalk Loc B: sec H surjective
-- statement:
--   The Stalk Loc B construction uses the sec H surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L19-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLocB.lean#L19-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
open ReciprocityTheory.AnForm.R.StalkLocB
variable {W : Scheme.{0}} (V : W.Opens) {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
  (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ K)))

theorem ReciprocityTheory.AnForm.R.StalkLocB.secH_surjective : Function.Surjective (secH V K iso) := by sorry
