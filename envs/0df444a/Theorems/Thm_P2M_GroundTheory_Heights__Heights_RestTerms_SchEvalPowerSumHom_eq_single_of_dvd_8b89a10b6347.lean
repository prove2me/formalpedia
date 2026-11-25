-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchEvalPowerSumHom_eq_single_of_dvd_8b89a10b6347
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchEvalPowerSumHom_eq_single_of_dvd_8b89a10b6347
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:09.823572+00:00
-- url     : https://prove2.me/theorems/9d53d408-75aa-41aa-b2ca-e068d11e1328
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Eval Power Sum Hom eq single of dvd 8b89a10b6347: P2 M Ground Theory Heights  Heights Rest Terms Sch Eval Power Sum Hom eq single of dvd 8b89a10b6347
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Eval Power Sum Hom eq single of dvd 8b89a10b6347 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Eval Power Sum Hom eq single of dvd 8b89a10b6347 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchEvalPowerSumHom.lean#L10-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchEvalPowerSumHom.lean#L10-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchEvalPowerSumHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchEvalPowerSumHom_eq_single_of_dvd_8b89a10b6347 {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (e : Fin N →₀ ℕ) (hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = k)
    (hd : ∀ i ∈ e.support, k ∣ (i : ℕ) + 1) :
    e = Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchEvalPowerSumHom».«eq_single_of_dvd» := P2M_GroundTheory_Heights__Heights_RestTerms_SchEvalPowerSumHom_eq_single_of_dvd_8b89a10b6347
