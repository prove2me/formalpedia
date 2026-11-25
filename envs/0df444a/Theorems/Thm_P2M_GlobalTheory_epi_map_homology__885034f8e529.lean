-- Prove2me | Theorems.Thm_P2M_GlobalTheory_epi_map_homology__885034f8e529
-- name    : P2M_GlobalTheory_epi_map_homology__885034f8e529
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:06:53.576207+00:00
-- url     : https://prove2.me/theorems/b39cbdec-9ae9-4ea3-b670-c9b0fb26e7e1
-- title:
--   P2 M Global Theory epi map homology  885034f8e529: P2 M Global Theory epi map homology  885034f8e529
-- statement:
--   The P2 M Global Theory epi map homology  885034f8e529 construction uses the P2 M Global Theory epi map homology  885034f8e529 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L194-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndKerBaseChangeOfForallResidueField.lean#L194-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
open CategoryTheory Category Limits
set_option backward.isDefEq.respectTransparency false
variable {C D : Type*} [Category* C] [Category* D]
variable [HasZeroMorphisms C] [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable [PreservesColimitsOfShape WalkingParallelPair F]

theorem P2M_GlobalTheory_epi_map_homology__885034f8e529 (S : ShortComplex C) [S.HasHomology] : Epi (F.map S.homologyπ) := by sorry

alias «GlobalTheory».«epi_map_homologyπ» := P2M_GlobalTheory_epi_map_homology__885034f8e529
