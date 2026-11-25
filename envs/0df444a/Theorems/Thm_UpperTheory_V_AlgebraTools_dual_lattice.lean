-- Prove2me | Theorems.Thm_UpperTheory_V_AlgebraTools_dual_lattice
-- name    : UpperTheory.V.AlgebraTools.dual_lattice
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:40:45.029829+00:00
-- url     : https://prove2.me/theorems/ad757d62-b1bf-4aea-b817-7e3a434e2046
-- title:
--   Algebra Tools: dual lattice
-- statement:
--   The Algebra Tools construction uses the dual lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/AlgebraTools/DualLattice.lean#L21-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/AlgebraTools/DualLattice.lean#L21-L60

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DualLatticeDenominator
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_AlgebraTools_DualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.dual_lattice :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] (Bf : LinearMap.BilinForm F V), Bf.IsSymm → Bf.Nondegenerate → ∀ Y : Submodule A V, Submodule.IsLattice F Y → Submodule.IsLattice F (Bf.dualSubmodule Y) ∧ Bf.dualSubmodule (Bf.dualSubmodule Y) = Y ∧ ∀ Z : Submodule A V, Submodule.IsLattice F Z → ∃ s : ℕ, maximalIdeal A ^ s • Z ≤ Y := by sorry
