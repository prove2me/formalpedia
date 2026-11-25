-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UniformSerre_isHomogeneous_sub__7c16f7263714
-- name    : P2M_GlobalTheory_UniformSerre_isHomogeneous_sub__7c16f7263714
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:17:22.435343+00:00
-- url     : https://prove2.me/theorems/abc32751-826c-5ea5-b812-6d672e677705
-- title:
--   P2 M Global Theory Uniform Serre is Homogeneous sub  7c16f7263714: P2 M Global Theory Uniform Serre is Homogeneous sub  7c16f7263714
-- statement:
--   The P2 M Global Theory Uniform Serre is Homogeneous sub  7c16f7263714 construction uses the P2 M Global Theory Uniform Serre is Homogeneous sub  7c16f7263714 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UniformSerreSections.lean#L76-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHomogeneousIdealOverReesAlgebraStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormOfCompatibleFractionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UniformSerreSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.UniformSerre
variable {R : Type} [CommRing R] {I : Ideal R} {σ : Type}

theorem P2M_GlobalTheory_UniformSerre_isHomogeneous_sub__7c16f7263714 {S : Type} [CommRing S] {P Q : MvPolynomial σ S} {t : ℕ}
    (hP : P.IsHomogeneous t) (hQ : Q.IsHomogeneous t) : (P - Q).IsHomogeneous t := by sorry

alias «GlobalTheory».«UniformSerre».«isHomogeneous_sub'» := P2M_GlobalTheory_UniformSerre_isHomogeneous_sub__7c16f7263714
