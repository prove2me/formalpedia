-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_zero2
-- name    : ReciprocityTheory.PGsh.OAdj.e_zero2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:46.644336+00:00
-- url     : https://prove2.me/theorems/af1046b5-87d9-49fc-b5e2-b330261604a4
-- title:
--   OAdj: e zero2
-- statement:
--   The OAdj construction uses the e zero2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L38-L46

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

theorem ReciprocityTheory.PGsh.OAdj.e_zero2 (x : B.G R) : HEq (A.e s x 0 (B.zero2 (A.a.f s x))) (B.zero2 x) := by sorry
