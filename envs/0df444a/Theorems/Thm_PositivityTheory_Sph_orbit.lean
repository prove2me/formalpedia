-- Prove2me | Theorems.Thm_PositivityTheory_Sph_orbit
-- name    : PositivityTheory.Sph.orbit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:04:06.620664+00:00
-- url     : https://prove2.me/theorems/3c0ca35e-541e-551b-8bd5-80a11dabfdb8
-- title:
--   Sph: orbit
-- statement:
--   The Sph construction uses the orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/ExistsIsUnitAddMul.lean#L68-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/SphericalLattices/ExistsIsUnitAddMul.lean#L68-L127

import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_LatDefs
import Definitions.Def_Development_WeilBound_ThetaLifts_SphericalLattices_ExistsIsUnitAddMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Sph
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem PositivityTheory.Sph.orbit {n d : ℕ} {t : k} {Y Y' : Matrix (Fin n) (Fin d) k} (h1 : Below t Y Y') (h2 : Below t Y' Y) :
    ∃ U : Matrix (Fin n) (Fin n) 𝒪[k], IsUnit U.det ∧ ∃ Z, IntM Z ∧ Y = U.map (algebraMap 𝒪[k] k) * Y' + t • Z := by sorry
