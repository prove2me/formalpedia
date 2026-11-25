-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_HomogeneousCochainIso_eFun_succ
-- name    : ReciprocityTheory.Coh.HomogeneousCochainIso.eFun_succ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:51:02.072258+00:00
-- url     : https://prove2.me/theorems/bfbe4783-2d08-4254-83af-540d67dd8c68
-- title:
--   Homogeneous Cochain Iso: e Fun succ
-- statement:
--   The Homogeneous Cochain Iso construction uses the e Fun succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HomogIso.lean#L116-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/HomogIso.lean#L116-L131

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

theorem ReciprocityTheory.Coh.HomogeneousCochainIso.eFun_succ (M : TRep R G) (n : ℕ) (f : (Fin n → G) → M.V) (x : Fin (n + 2) → G)
    (j : Fin (n + 1)) :
    eFun M n f (fun k => x (j.succ.succAbove k)) =
      M.rho (x 0) (f (Fin.contractNth j (· * ·) fun i => (x i.castSucc)⁻¹ * x i.succ)) := by sorry
