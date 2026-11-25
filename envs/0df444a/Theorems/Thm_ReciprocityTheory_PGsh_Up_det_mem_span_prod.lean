-- Prove2me | Theorems.Thm_ReciprocityTheory_PGsh_Up_det_mem_span_prod
-- name    : ReciprocityTheory.PGsh.Up.det_mem_span_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:25.363127+00:00
-- url     : https://prove2.me/theorems/30309f98-dfd3-4b24-a3ca-faffa9defac7
-- title:
--   Up: det mem span prod
-- statement:
--   The Up construction uses the det mem span prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsLocalOfIntegers.lean#L23-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/IsLocalOfIntegers.lean#L23-L159

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up

theorem ReciprocityTheory.PGsh.Up.det_mem_span_prod {R : Type*} [CommRing R] [IsLocalRing R] :
    ∀ (m : ℕ) (c : Fin m → R) (n : ℕ) (q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j})),
      Submodule.span R (Set.range q) = ⊤ →
      ∀ T : Matrix (Fin n) (Fin n) R, (∀ k, ∑ i, T k i • q i = 0) →
      T.det ∈ Ideal.span {∏ j, c j} := by sorry
