-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_sobolev_representation_prodExp__478ce11e1a4a
-- name    : P2M_GlobalTheory_T_exists_sobolev_representation_prodExp__478ce11e1a4a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:37:56.736324+00:00
-- url     : https://prove2.me/theorems/b1f56679-abca-4683-a98d-6b982d75a7be
-- title:
--   P2 M Global Theory T exists sobolev representation prod Exp  478ce11e1a4a: P2 M Global Theory T exists sobolev representation prod Exp  478ce11e1a4a
-- statement:
--   The P2 M Global Theory T exists sobolev representation prod Exp  478ce11e1a4a construction uses the P2 M Global Theory T exists sobolev representation prod Exp  478ce11e1a4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSobolevRepresentationProdExpStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSobolevRepresentationProdExpStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExp
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExpStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_sobolev_representation_prodExp__478ce11e1a4a : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (ε : ℝ), 0 < ε → ∀ (n : ℕ) (X : Fin n → 𝔤), ∃ (N : ℕ) (l : Fin N → List 𝔤) (κ : Fin N → (Fin n → ℝ) → ℂ), (∀ i, Continuous (κ i) ∧ tsupport (κ i) ⊆ Metric.closedBall 0 ε) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ g, f g = ∑ i, ∫ t, κ i t * (l i).foldr h.rightDeriv f (g * h.prodExp X t) := by sorry

alias «GlobalTheory».«T».«exists_sobolev_representation_prodExp'» := P2M_GlobalTheory_T_exists_sobolev_representation_prodExp__478ce11e1a4a
