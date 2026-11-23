-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_det_sq_eq
-- name    : ReciprocityTheory.PGsh.det_sq_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:36.269724+00:00
-- url     : https://prove2.me/theorems/855a58af-0a1a-469d-b224-a008c967e118
-- title:
--   PGsh: det sq eq
-- statement:
--   The PGsh construction uses the det sq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ThmAUses.lean#L25-L34

import Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
import Definitions.Def_ReciprocityTheory_DualLattices_VDetEqOneOfIntegral
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAUses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {D : Type} [CommRing D] {g : ℕ}

theorem ReciprocityTheory.PGsh.det_sq_eq (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D)
    (hJ : Φᵀ * stdJ D g * Φ = c • E) :
    Φ.det ^ 2 = c ^ (2 * g) * (E.det * (stdJ D g).det) := by sorry
