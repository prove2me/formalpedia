-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_C2_entry_embedMatrix
-- name    : PI.OneCosetSharp.W.C2.entry_embedMatrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:01.746803+00:00
-- url     : https://prove2.me/theorems/97e31e39-85fc-4fd8-be0f-ed1bd450cd84
-- title:
--   C2: entry embed Matrix
-- statement:
--   The C2 construction uses the entry embed Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/EntryEmbedMatrix.lean#L35-L44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_EntryEmbedMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.C2
open Loc LocE
variable {k : Type} [Field k]

theorem PI.OneCosetSharp.W.C2.entry_embedMatrix {n' c n : ℕ} (k₀ : ℕ) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (τ : FC n' (c + 1) n c → k)
    (p p' : ℕ) (hp : fIdx k₀ c n p < n + c) (hp' : fIdx k₀ (c + 1) n' p' < n' + (c + 1)) :
    ent k₀ (c + 1) n' c n (xx1 xj τ) p p' =
      (if hf : IsFree n' n c (fIdx k₀ c n p) (fIdx k₀ (c + 1) n' p') then τ ⟨(⟨_, hp⟩, ⟨_, hp'⟩), hf⟩
       else if hs : fIdx k₀ (c + 1) n' p' < n' then
          (if hl : fIdx k₀ c n p < n then LinearMap.toMatrix' xj ⟨_, hl⟩ ⟨_, hs⟩ else 0)
       else if fIdx k₀ c n p = n + (fIdx k₀ (c + 1) n' p' - n') then 1 else 0) := by sorry
