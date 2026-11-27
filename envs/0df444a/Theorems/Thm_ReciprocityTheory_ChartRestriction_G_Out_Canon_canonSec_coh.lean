-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_canonSec_coh
-- name    : ReciprocityTheory.ChartRestriction.G.Out.Canon.canonSec_coh
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:21:05.038531+00:00
-- url     : https://prove2.me/theorems/f8f0f1fc-d6a6-49b6-854a-693a68ca749b
-- title:
--   Canon: canon Sec coh
-- statement:
--   The Canon construction uses the canon Sec coh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean#L327-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean#L327-L347

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out.Canon
variable {X Y : Scheme.{0}} (L : LB X)
variable {L}
variable {K K' : Type} [Fintype K] [Fintype K']
variable (L)
variable {L}
variable (L)

theorem ReciprocityTheory.ChartRestriction.G.Out.Canon.canonSec_coh (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (hs : LB.SameSum φ ε φ' ε') (hsub : ∀ k, ∃ k', φ' k' = φ k)
    (sc : LB.Sec (LB.LinComb L φ ε)) (j : (LB.LinComb L φ ε).ι) (j' : (LB.LinComb L φ' ε').ι)
    (hj' : LB.Coh L φ' j') (hjj' : ∀ k k', φ k = φ' k' → j k = j' k') :
    rO (inf_le_left : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ' ε').U j' ≤ _) (sc.f j) =
      rO (inf_le_right : (LB.LinComb L φ ε).U j ⊓ (LB.LinComb L φ' ε').U j' ≤ _)
        ((canonSec L hL φ ε φ' ε' hs hsub sc).f j') := by sorry
