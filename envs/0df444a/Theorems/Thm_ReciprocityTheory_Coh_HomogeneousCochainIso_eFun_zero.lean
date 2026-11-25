-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_HomogeneousCochainIso_eFun_zero
-- name    : ReciprocityTheory.Coh.HomogeneousCochainIso.eFun_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:49:41.284099+00:00
-- url     : https://prove2.me/theorems/9454f4f1-0c64-549a-afb0-f2a3328d4c34
-- title:
--   Homogeneous Cochain Iso: e Fun zero
-- statement:
--   The Homogeneous Cochain Iso construction uses the e Fun zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HomogIso.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HomogIso.lean#L109-L114

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
open ReciprocityTheory.Coh.HomogeneousCochainIso
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem ReciprocityTheory.Coh.HomogeneousCochainIso.eFun_zero (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 2) → G) :
    eFun M n f (fun k => x (Fin.succAbove 0 k)) =
      M.rho (x 0) (M.rho ((x (0 : Fin (n + 1)).castSucc)⁻¹ * x (0 : Fin (n + 1)).succ)
        (f fun i => (x i.succ.castSucc)⁻¹ * x i.succ.succ)) := by sorry
