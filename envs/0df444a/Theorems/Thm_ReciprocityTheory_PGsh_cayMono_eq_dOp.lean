-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_cayMono_eq_dOp
-- name    : ReciprocityTheory.PGsh.cayMono_eq_dOp
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:47.928091+00:00
-- url     : https://prove2.me/theorems/8ed5dd35-0276-438b-a9df-d239eb3048a3
-- title:
--   PGsh: cay Mono eq d Op
-- statement:
--   The PGsh construction uses the cay Mono eq d Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L130-L132

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.PGsh.cayMono_eq_dOp (σ : Equiv.Perm (Fin n)) : cayMono n R σ = dOp σ id := by sorry
