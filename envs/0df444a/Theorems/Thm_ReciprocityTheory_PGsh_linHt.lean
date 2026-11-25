-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_linHt
-- name    : ReciprocityTheory.PGsh.linHt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:35.797968+00:00
-- url     : https://prove2.me/theorems/6d7c5966-7923-4d47-9ae6-fbac69fb21c6
-- title:
--   PGsh: lin Ht
-- statement:
--   The PGsh construction uses the lin Ht property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L240-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SubMemSpan.lean#L240-L241

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

theorem ReciprocityTheory.PGsh.linHt (B : BX R₀) (O : LAlg R₀) : LinHtStatement B O := by sorry
