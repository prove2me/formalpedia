-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_b4
-- name    : ReciprocityTheory.PGsh.b4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:49.480386+00:00
-- url     : https://prove2.me/theorems/5a59bf95-b766-4f98-94aa-37cf18984e33
-- title:
--   PGsh: b4
-- statement:
--   The PGsh construction uses the b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/OneAddPowOfSq.lean#L32-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/OneAddPowOfSq.lean#L32-L86

import Definitions.Def_ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_OneAddPowOfSq
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

theorem ReciprocityTheory.PGsh.b4 (B : BX R₀) (hB1 : PairingPropertiesStatement B) (hB3 : TangentPairingStatement B) {p : ℕ}
    (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw := by sorry
