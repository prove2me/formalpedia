-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_LHom_sqZero_of_span
-- name    : ReciprocityTheory.PGsh.LHom.sqZero_of_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:46.212315+00:00
-- url     : https://prove2.me/theorems/8116353b-0e02-419b-be06-abbceb5d0066
-- title:
--   LHom: sq Zero of span
-- statement:
--   The LHom construction uses the sq Zero of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SqZeroOfSpan.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SqZeroOfSpan.lean#L36-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
universe u
attribute [instance] LAlg.cr LAlg.alg LAlg.loc
variable {R₀ : Type u} [CommRing R₀]

theorem ReciprocityTheory.PGsh.LHom.sqZero_of_span {R S : LAlg R₀} (π : LHom R S) (ξ : (R : Type u))
    (hs : Function.Surjective π.1) (hk : RingHom.ker π.1 = Ideal.span {ξ}) (hξ : ξ * ξ = 0) :
    π.SqZero := by sorry
