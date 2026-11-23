-- Prove2me | Theorems.Thm_P2M_Formalism_L2_Col_GSD_Slice_card_stab_smul__ace3a7f01b1e
-- name    : P2M_Formalism_L2_Col_GSD_Slice_card_stab_smul__ace3a7f01b1e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:38.868594+00:00
-- url     : https://prove2.me/theorems/086a38ae-a3f3-4c81-9816-2c2d2b5ae05c
-- title:
--   P2 M Formalism L2 Col GSD Slice card stab smul  ace3a7f01b1e: P2 M Formalism L2 Col GSD Slice card stab smul  ace3a7f01b1e
-- statement:
--   The P2 M Formalism L2 Col GSD Slice card stab smul  ace3a7f01b1e construction uses the P2 M Formalism L2 Col GSD Slice card stab smul  ace3a7f01b1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L847-L852
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L847-L852

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (S : GSD K)
variable (A : Type) [Group A] [MulAction A S.D]
open Formalism.L2.Col.GSD.Slice
variable {S A} (σ : S.Slice A)
variable [SMulCommClass A S.G S.D]

theorem P2M_Formalism_L2_Col_GSD_Slice_card_stab_smul__ace3a7f01b1e (b : A) (d : S.D) :
    Nat.card (MulAction.stabilizer S.G (b • d)) = Nat.card (MulAction.stabilizer S.G d) := by sorry

alias «Formalism».«L2».«Col».«GSD».«Slice».«card_stab_smul'» := P2M_Formalism_L2_Col_GSD_Slice_card_stab_smul__ace3a7f01b1e
