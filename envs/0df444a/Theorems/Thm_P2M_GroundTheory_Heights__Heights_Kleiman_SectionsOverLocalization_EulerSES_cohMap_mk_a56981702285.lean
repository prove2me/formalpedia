-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_cohMap_mk_a56981702285
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_cohMap_mk_a56981702285
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:08.476809+00:00
-- url     : https://prove2.me/theorems/e1770081-51e0-4844-b880-f99c3fb345a3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES coh Map mk a56981702285: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES coh Map mk a5
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES coh Map mk a56981702285 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES coh Map mk a56981702285 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L73-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/CohMkEqZero.lean#L73-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CohMkEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.EulerSES
open Module
variable {F : Type} [Field F] {X Y : ℕ → Type} [∀ n, AddCommGroup (X n)] [∀ n, Module F (X n)]
  [∀ n, AddCommGroup (Y n)] [∀ n, Module F (Y n)]
variable (CX : ∀ n, Submodule F (X n)) (dX : ∀ n, X n →ₗ[F] X (n + 1))
  (CY : ∀ n, Submodule F (Y n)) (dY : ∀ n, Y n →ₗ[F] Y (n + 1)) (h : ∀ n, X n →ₗ[F] Y n)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_cohMap_mk_a56981702285 (hC : ∀ n, ∀ x ∈ CX n, h n x ∈ CY n)
    (hd : ∀ n, ∀ x ∈ CX n, dY n (h n x) = h (n + 1) (dX n x)) (n : ℕ) (x : cyc CX dX n) :
    cohMap CX dX CY dY h hC hd n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨h n x, map_mem_cyc CX dX CY dY h hC hd n x x.2⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«EulerSES».«cohMap_mk» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_cohMap_mk_a56981702285
