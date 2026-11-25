-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_homog_eq
-- name    : ReciprocityTheory.Coh.CCA.homog_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:19.777007+00:00
-- url     : https://prove2.me/theorems/83f431b5-b442-4057-9037-0db74d37d2b0
-- title:
--   CCA: homog eq
-- statement:
--   The CCA construction uses the homog eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L258-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L258-L277

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorA
import Definitions.Def_ReciprocityTheory_GroupCohomology_CupCorB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.CCA
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)

theorem ReciprocityTheory.Coh.CCA.homog_eq {P : TRep R G} (e : ∀ n, P.coch.X n ≃ₗ[R] hcoch P G n)
    (h1 : ∀ n f x, (e n f).1 x = P.rho (x 0) (f.1 fun i => (x i.castSucc)⁻¹ * x i.succ)) (n : ℕ)
    (f : P.coch.X n) (F : (Fin (n + 1) → G) → P.V) (hF : F ∈ hcoch P G n)
    (hf : ∀ g, f.1 g = F (Fin.partialProd g)) : (e n f).1 = F := by sorry
