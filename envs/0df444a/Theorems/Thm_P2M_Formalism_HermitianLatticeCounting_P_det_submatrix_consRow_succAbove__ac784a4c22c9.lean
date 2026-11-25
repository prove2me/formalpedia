-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_det_submatrix_consRow_succAbove__ac784a4c22c9
-- name    : P2M_Formalism_HermitianLatticeCounting_P_det_submatrix_consRow_succAbove__ac784a4c22c9
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:31.860681+00:00
-- url     : https://prove2.me/theorems/e990a21f-1d42-4bee-8a95-05fbd4c5b063
-- title:
--   P2 M Formalism Hermitian Lattice Counting P det submatrix cons Row succ Above  ac784a4c22c9: P2 M Formalism Hermitian Lattice Counting P det submatrix cons Row succ Above  ac784a4c22c9
-- statement:
--   The P2 M Formalism Hermitian Lattice Counting P det submatrix cons Row succ Above  ac784a4c22c9 construction uses the P2 M Formalism Hermitian Lattice Counting P det submatrix cons Row succ Above  ac784a4c22c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L219-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/DetMulEqSumProdMulDetSubmatrix.lean#L219-L225

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem P2M_Formalism_HermitianLatticeCounting_P_det_submatrix_consRow_succAbove__ac784a4c22c9 {R : Type*} [CommRing R] {r : ℕ} (Y : Matrix (Fin r) (Fin (r + 1)) R)
    (u : Fin (r + 1) → R) (b₀ : Fin (r + 1)) (a : Fin r) :
    ((consRowMatrix u Y).submatrix a.succ.succAbove b₀.succAbove).det =
      (-1) ^ (a : ℕ) * ∑ c, u (b₀.succAbove c) * (Y.submatrix id b₀.succAbove).adjugate c a := by sorry

alias «Formalism».«HermitianLatticeCounting».«P».«det_submatrix_consRow_succAbove'» := P2M_Formalism_HermitianLatticeCounting_P_det_submatrix_consRow_succAbove__ac784a4c22c9
