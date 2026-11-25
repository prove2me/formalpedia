-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_L2_map_fourier_spanCols
-- name    : ReciprocityTheory.PGsh.L2.map_fourier_spanCols
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:06:16.732843+00:00
-- url     : https://prove2.me/theorems/b6879e4f-7422-4b18-bb99-cbfd8e785f49
-- title:
--   L2: map fourier span Cols
-- statement:
--   The L2 construction uses the map fourier span Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/MemDualLatMapFourier.lean#L30-L47

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

theorem ReciprocityTheory.PGsh.L2.map_fourier_spanCols (e : H ≃ AddChar N C) (σ : H ≃ N) (Dm : Matrix N N C) :
    (Submodule.span R (Set.range fun j x => Dm x j)).map (fourier (R := R) fun h a => e h a) =
      Submodule.span R (Set.range fun k h => ((tableM e σ)ᵀ * Dm).submatrix σ σ h k) := by sorry
