-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_harmK_map
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:02.294796+00:00
-- url     : https://prove2.me/theorems/495a743a-d42e-4ec9-a3a1-3df2616611ba
-- title:
--   Pullback Sections: harm K map
-- statement:
--   The Pullback Sections construction uses the harm K map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/FFVMap.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/FFVMap.lean#L58-L67

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map (io : k →+* K) {cc : Ty → Ty} {isX : Ty → Prop} {P : MvPolynomial (Letter Ty r n) k}
    (hP : P ∈ harmK r n k cc isX (fun _ => 1)) : P.map io ∈ harmK r n K cc isX (fun _ => 1) := by sorry
