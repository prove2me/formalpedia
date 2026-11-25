-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_cayOp_map
-- name    : ReciprocityTheory.PGsh.cayOp_map
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:49.295871+00:00
-- url     : https://prove2.me/theorems/118fd74d-4b30-412c-b7d9-1c5870978525
-- title:
--   PGsh: cay Op map
-- statement:
--   The PGsh construction uses the cay Op map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L441-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/DetPolyMulCayleyOmegaPow.lean#L441-L455

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

theorem ReciprocityTheory.PGsh.cayOp_map (p : MvPolynomial (Fin n × Fin n) ℤ) :
    cayOp n R (map (Int.castRingHom R) p) = map (Int.castRingHom R) (cayOp n ℤ p) := by sorry
