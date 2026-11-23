-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_BX_castFst_smul
-- name    : ReciprocityTheory.PGsh.BX.castFst_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:41.694635+00:00
-- url     : https://prove2.me/theorems/dd41f810-96ba-448c-9106-ee53e6add7a2
-- title:
--   BX: cast Fst smul
-- statement:
--   The BX construction uses the cast Fst smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsPairingValueAddRight.lean#L37-L40

import Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
import Definitions.Def_ReciprocityTheory_DualLattices_InstAddCommMonoidFibreFst
import Definitions.Def_ReciprocityTheory_DualLattices_NsmulFstAddSnd
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.BX
variable (B : BX R₀) {R : LAlg R₀}

theorem ReciprocityTheory.PGsh.BX.castFst_smul {a b y : B.G R} (h : a = b) (l : (R : Type u)ˣ) (u : B.P R a y) :
    B.tr1 h (B.smul l u) = B.smul l (B.tr1 h u) := by sorry
