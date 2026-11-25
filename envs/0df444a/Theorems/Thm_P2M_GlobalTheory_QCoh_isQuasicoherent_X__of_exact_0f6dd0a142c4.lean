-- Prove2me | Theorems.Thm_P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_0f6dd0a142c4
-- name    : P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_0f6dd0a142c4
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:28.142805+00:00
-- url     : https://prove2.me/theorems/23db5387-12d2-4fab-b27f-261f22bd8170
-- title:
--   P2 M Global Theory QCoh is Quasicoherent X  of exact 0f6dd0a142c4: P2 M Global Theory QCoh is Quasicoherent X  of exact 0f6dd0a142c4
-- statement:
--   The P2 M Global Theory QCoh is Quasicoherent X  of exact 0f6dd0a142c4 construction uses the P2 M Global Theory QCoh is Quasicoherent X  of exact 0f6dd0a142c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L241-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L241-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}

theorem P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_0f6dd0a142c4 {S : ShortComplex X.Modules} (hS : S.Exact) [Mono S.f]
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₁.IsQuasicoherent := by sorry

alias «GlobalTheory».«QCoh».«isQuasicoherent_X₁_of_exact» := P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_0f6dd0a142c4
