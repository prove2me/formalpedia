-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_gaussPoint__74b33421a490
-- name    : P2M_GlobalTheory_T_exists_gaussPoint__74b33421a490
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:06:47.562706+00:00
-- url     : https://prove2.me/theorems/9bfce780-41fc-5910-a8e4-b64866c4103a
-- title:
--   P2 M Global Theory T exists gauss Point  74b33421a490: P2 M Global Theory T exists gauss Point  74b33421a490
-- statement:
--   The P2 M Global Theory T exists gauss Point  74b33421a490 construction uses the P2 M Global Theory T exists gauss Point  74b33421a490 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGaussPointStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsGaussPointStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPoint
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsGaussPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_gaussPoint__74b33421a490 : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧ IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧ (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧ ∀ x, vV T'.V (i x) = vV T.V x := by sorry

alias «GlobalTheory».«T».«exists_gaussPoint'» := P2M_GlobalTheory_T_exists_gaussPoint__74b33421a490
