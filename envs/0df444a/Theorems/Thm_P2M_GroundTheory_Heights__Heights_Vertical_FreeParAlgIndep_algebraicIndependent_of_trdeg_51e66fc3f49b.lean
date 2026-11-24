-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_algebraicIndependent_of_trdeg_51e66fc3f49b
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_algebraicIndependent_of_trdeg_51e66fc3f49b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:50.896253+00:00
-- url     : https://prove2.me/theorems/c10637a9-c270-44ee-be19-d619eced0735
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Free Par Alg Indep algebraic Independent of trdeg 51e66fc3f49b: P2 M Ground Theory Heights  Heights Vertical Free Par Alg Indep algebraic Independent of tr
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Free Par Alg Indep algebraic Independent of trdeg 51e66fc3f49b construction uses the P2 M Ground Theory Heights  Heights Vertical Free Par Alg Indep algebraic Independent of trdeg 51e66fc3f49b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFreeParAlgIndep.lean#L25-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PFreeParAlgIndep.lean#L25-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PFreeParAlgIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial Cardinal
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.FreeParAlgIndep

theorem P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_algebraicIndependent_of_trdeg_51e66fc3f49b {k L : Type} [Field k] [Field L] [Algebra k L]
    (A₀ : Subalgebra k L) {ι : Type} [Finite ι] (w : ι → L)
    [Algebra.IsAlgebraic (Algebra.adjoin A₀ (Set.range w)) L] {e : ℕ}
    (htr : Algebra.trdeg k A₀ ≤ e) (hle : (e : Cardinal) + #ι ≤ Algebra.trdeg k L) :
    AlgebraicIndependent A₀ w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«FreeParAlgIndep».«algebraicIndependent_of_trdeg» := P2M_GroundTheory_Heights__Heights_Vertical_FreeParAlgIndep_algebraicIndependent_of_trdeg_51e66fc3f49b
