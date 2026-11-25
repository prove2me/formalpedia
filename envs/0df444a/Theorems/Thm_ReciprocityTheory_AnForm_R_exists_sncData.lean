-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_sncData
-- name    : ReciprocityTheory.AnForm.R.exists_sncData
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:45:47.238426+00:00
-- url     : https://prove2.me/theorems/9896581f-8dc8-5cee-9c3e-1d72dbf98ca8
-- title:
--   R: exists snc Data
-- statement:
--   The R construction uses the exists snc Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L149-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L149-L267

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
variable {W : Scheme.{0}}
variable {s : W ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.exists_sncData [IsNoetherian W] [LocallyOfFiniteType s] {Z : W.IdealSheafData}
    (hZ : FinalTheorems.Snc Z) (P : AffPres s) {rc : ℕ} (c : Fin rc ≃ comps (Z.support : Set W)) (e : ℕ)
    (x : W) (hx : x ∈ P.V) (hcl : IsClosed ({x} : Set W))
    (hdim : ringKrullDim (W.presheaf.stalk x) = e) :
    ∃ S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc,
      (∀ l ∈ S.J, ∃ k, S.σ l = some k ∧ IsBranch (Z.support : Set W) (P.secHom (S.r l)) x (c k)) ∧
      ∃ O : W.Opens, x ∈ O ∧ O ≤ P.V ∧
      ∀ k (y : W) (hy : y ∈ P.V), y ∈ O → IsClosed ({y} : Set W) →
        (y ∈ (c k : Set W) ↔ ∃ l, S.σ l = some k ∧ eval (P.coord y hy) (S.r l) = 0) := by sorry
