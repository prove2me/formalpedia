-- Prove2me | Theorems.Thm_P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_d7721705b427
-- name    : P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_d7721705b427
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:10.129481+00:00
-- url     : https://prove2.me/theorems/0f03dbc3-2797-408e-a30d-672665d88df0
-- title:
--   P2 M Global Theory QCoh is Quasicoherent X  of exact d7721705b427: P2 M Global Theory QCoh is Quasicoherent X  of exact d7721705b427
-- statement:
--   The P2 M Global Theory QCoh is Quasicoherent X  of exact d7721705b427 construction uses the P2 M Global Theory QCoh is Quasicoherent X  of exact d7721705b427 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L246-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L246-L248

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

theorem P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_d7721705b427 {S : ShortComplex X.Modules} (hS : S.Exact) [Epi S.g]
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] : S.X₃.IsQuasicoherent := by sorry

alias «GlobalTheory».«QCoh».«isQuasicoherent_X₃_of_exact» := P2M_GlobalTheory_QCoh_isQuasicoherent_X__of_exact_d7721705b427
