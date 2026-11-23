-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_OAdj_e_zero1
-- name    : ReciprocityTheory.PGsh.OAdj.e_zero1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:41.490877+00:00
-- url     : https://prove2.me/theorems/dd72e091-ddda-4826-96a5-06b345b7aad6
-- title:
--   OAdj: e zero1
-- statement:
--   The OAdj construction uses the e zero1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L23-L36

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

theorem ReciprocityTheory.PGsh.OAdj.e_zero1 (z : B.G R) :
    HEq (A.e s 0 z (B.tr1 (map_zero (A.a.f s)).symm (B.zero1 z))) (B.zero1 (A.ab.f s z)) := by sorry
