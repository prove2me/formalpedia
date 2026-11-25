-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_nsmul2
-- name    : ReciprocityTheory.PGsh.OAdj.e_nsmul2
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:05.969857+00:00
-- url     : https://prove2.me/theorems/8b5ffd95-6c76-496c-98f0-aae8748dfd00
-- title:
--   OAdj: e nsmul2
-- statement:
--   The OAdj construction uses the e nsmul2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L68-L78

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

theorem ReciprocityTheory.PGsh.OAdj.e_nsmul2 (x z : B.G R) (u : B.P R (A.a.f s x) z) (n : ℕ) :
    HEq (A.e s x (n • z) (B.nsmul2 u n)) (B.nsmul2 (A.e s x z u) n) := by sorry
