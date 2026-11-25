-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_eval_aeval__5dda70722a7a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_eval_aeval__5dda70722a7a
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:16:35.224952+00:00
-- url     : https://prove2.me/theorems/04deb1e9-1612-5f0a-a0dc-f77232e8b00e
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pullback Sections eval aeval  5dda70722a7a: P2 M Reciprocity Theory Chart Restriction G Pullback Sections eval aeval  5dda70722a7a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pullback Sections eval aeval  5dda70722a7a construction uses the P2 M Reciprocity Theory Chart Restriction G Pullback Sections eval aeval  5dda70722a7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/FFVMap.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/FFVMap.lean#L16-L21

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Mathlib.Algebra.MvPolynomial.Funext
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_FFVMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open NumberField IsDedekindDomain Formalism.L2.Pj MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k K : Type} [Field k] [Field K]

theorem P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_eval_aeval__5dda70722a7a {ι κ : Type} (g : ι → MvPolynomial κ k) (x : κ → k) (Q : MvPolynomial ι k) :
    eval x (aeval g Q) = eval (fun ℓ => eval x (g ℓ)) Q := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«PullbackSections».«eval_aeval'» := P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_eval_aeval__5dda70722a7a
