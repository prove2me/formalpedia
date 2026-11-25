-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_nsmul1
-- name    : ReciprocityTheory.PGsh.OAdj.e_nsmul1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:57.1189+00:00
-- url     : https://prove2.me/theorems/68c6320e-022b-4416-afed-07edcc901e49
-- title:
--   OAdj: e nsmul1
-- statement:
--   The OAdj construction uses the e nsmul1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L48-L66

import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
open ReciprocityTheory.PGsh.OAdj
variable {B : BX R₀} {O : LAlg R₀} (A : OAdj B O) {R : LAlg R₀} (s : LHom O R)

theorem ReciprocityTheory.PGsh.OAdj.e_nsmul1 (x z : B.G R) (u : B.P R (A.a.f s x) z) (n : ℕ)
    (w : B.P R (A.a.f s (n • x)) z) (hw : HEq w (B.nsmul1 u n)) :
    HEq (A.e s (n • x) z w) (B.nsmul1 (A.e s x z u) n) := by sorry
