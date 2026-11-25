-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_CCA_cup_cor_eq
-- name    : ReciprocityTheory.Coh.CCA.cup_cor_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:45.490535+00:00
-- url     : https://prove2.me/theorems/3fa28911-e960-485d-b243-db9426d2fb4f
-- title:
--   CCA: cup cor eq
-- statement:
--   The CCA construction uses the cup cor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L162-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/CupCorB.lean#L162-L189

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
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {M N P : TRep R G}
  (U : Subgroup G) [U.FiniteIndex]

theorem ReciprocityTheory.Coh.CCA.cup_cor_eq (b : Pairing M N P) (p q : ℕ) (f : (Fin p → U) → M.V) (f' : (Fin q → G) → N.V)
    (g : Fin (p + q) → G) :
    cupFun b p q (corFun M U p f) f' g =
      normF P U (p + q) (hcup b.β p q (fun x => homz (M.resSub U).rho p f (fun i => retr U (x i)))
        (homz N.rho q f')) (Fin.partialProd g) := by sorry
