-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_complete_local_geomDomain__064aefd4eb68
-- name    : P2M_GlobalTheory_T_exists_complete_local_geomDomain__064aefd4eb68
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:07:37.226229+00:00
-- url     : https://prove2.me/theorems/7d4c50cc-d597-5431-b56c-7bf2f9412c39
-- title:
--   P2 M Global Theory T exists complete local geom Domain  064aefd4eb68: P2 M Global Theory T exists complete local geom Domain  064aefd4eb68
-- statement:
--   The P2 M Global Theory T exists complete local geom Domain  064aefd4eb68 construction uses the P2 M Global Theory T exists complete local geom Domain  064aefd4eb68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteLocalGeomDomainStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCompleteLocalGeomDomainStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteLocalGeomDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteLocalGeomDomainStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_complete_local_geomDomain__064aefd4eb68 : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k'] [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧ Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by sorry

alias «GlobalTheory».«T».«exists_complete_local_geomDomain'» := P2M_GlobalTheory_T_exists_complete_local_geomDomain__064aefd4eb68
