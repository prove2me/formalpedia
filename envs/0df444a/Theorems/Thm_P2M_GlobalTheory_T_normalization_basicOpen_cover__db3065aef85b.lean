-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_normalization_basicOpen_cover__db3065aef85b
-- name    : P2M_GlobalTheory_T_normalization_basicOpen_cover__db3065aef85b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:11:18.548349+00:00
-- url     : https://prove2.me/theorems/c24f7e22-ca04-4715-9065-ac7750ca0aa3
-- title:
--   P2 M Global Theory T normalization basic Open cover  db3065aef85b: P2 M Global Theory T normalization basic Open cover  db3065aef85b
-- statement:
--   The P2 M Global Theory T normalization basic Open cover  db3065aef85b construction uses the P2 M Global Theory T normalization basic Open cover  db3065aef85b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormalizationBasicOpenCoverStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormalizationBasicOpenCoverStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCover
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormalizationBasicOpenCoverStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_normalization_basicOpen_cover__db3065aef85b : ∀ (U X : Scheme.{0}) (f : U ⟶ X), ∀ [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [LocallyQuasiFinite f] (V : X.AffineZariskiSite), ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)), (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra; Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧ ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈ f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) := by sorry

alias «GlobalTheory».«T».«normalization_basicOpen_cover'» := P2M_GlobalTheory_T_normalization_basicOpen_cover__db3065aef85b
