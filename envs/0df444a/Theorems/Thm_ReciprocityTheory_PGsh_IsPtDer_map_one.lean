-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_IsPtDer_map_one
-- name    : ReciprocityTheory.PGsh.IsPtDer.map_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:12.853949+00:00
-- url     : https://prove2.me/theorems/4a3dc550-957e-4a23-81b7-650340ba1cf1
-- title:
--   Is Pt Der: map one
-- statement:
--   The Is Pt Der construction uses the map one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/RidConvolutionDerivation.lean#L63-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Bialgebra R A]

theorem ReciprocityTheory.PGsh.IsPtDer.map_one {δ : A →ₗ[R] R} (hδ : IsPtDer δ) : δ 1 = 0 := by sorry
