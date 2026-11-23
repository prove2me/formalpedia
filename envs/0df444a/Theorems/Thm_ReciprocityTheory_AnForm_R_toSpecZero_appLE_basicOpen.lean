-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_toSpecZero_appLE_basicOpen
-- name    : ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:47.038052+00:00
-- url     : https://prove2.me/theorems/ed7d52e3-efe3-4ec7-97a5-363bae0437d4
-- title:
--   R: to Spec Zero app LE basic Open
-- statement:
--   The R construction uses the to Spec Zero app LE basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L202-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjDehomA.lean#L202-L231

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SegreIdealIsHomogeneous
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable [Nonempty K]
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

theorem ReciprocityTheory.AnForm.R.toSpecZero_appLE_basicOpen {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫ (Proj.toSpecZero 𝒜).appLE ⊤ (Proj.basicOpen 𝒜 f) le_top =
      CommRingCat.ofHom (fromZeroRingHom 𝒜 (Submonoid.powers f)) ≫ Proj.awayToSection 𝒜 f := by sorry
