-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_tset_kV
-- name    : ReciprocityTheory.ChartRestriction.DS.tset_kV
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:30.576798+00:00
-- url     : https://prove2.me/theorems/a1472b5e-5196-588a-b280-9880c05680fb
-- title:
--   DS: tset k V
-- statement:
--   The DS construction uses the tset k V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L147-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/HidaSetting.lean#L147-L197

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_IsInLieAlgebraISmulAddConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Submodule ℂ H}

theorem ReciprocityTheory.ChartRestriction.DS.tset_kV {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {E : Fin n → Fin n → Module.End ℂ D} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (dual : Bool) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (f f' : Fin n → D)
    (h : (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H))) :
    (fun c => ((eeF dual E f' c : D) : H)) = kDiag dual σ k (fun c => ((eeF dual E f c : D) : H)) := by sorry
