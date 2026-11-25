-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_OAdj_pairing_iff
-- name    : ReciprocityTheory.PGsh.OAdj.pairing_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:06:27.022666+00:00
-- url     : https://prove2.me/theorems/387299d9-b017-59af-b24a-6168b394aec1
-- title:
--   OAdj: pairing iff
-- statement:
--   The OAdj construction uses the pairing iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L105-L110

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

theorem ReciprocityTheory.PGsh.OAdj.pairing_iff (N : ℕ) (x z : B.G R) (w : (R : Type u)ˣ) (hx : N • x = 0) (hz : N • z = 0) :
    B.IsPairing N (A.a.f s x) z w ↔ B.IsPairing N x (A.ab.f s z) w := by sorry
