-- Prove2me | Theorems.Thm_P2M_PI_MirrorSection__monomialMatrix_conjTranspose_6ef84c3c3930
-- name    : P2M_PI_MirrorSection__monomialMatrix_conjTranspose_6ef84c3c3930
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:57:21.524371+00:00
-- url     : https://prove2.me/theorems/3fa04a0f-c547-4732-b283-a4ca5a5d92c5
-- title:
--   P2 M PI Mirror Section  monomial Matrix conj Transpose 6ef84c3c3930: P2 M PI Mirror Section  monomial Matrix conj Transpose 6ef84c3c3930
-- statement:
--   The P2 M PI Mirror Section  monomial Matrix conj Transpose 6ef84c3c3930 construction uses the P2 M PI Mirror Section  monomial Matrix conj Transpose 6ef84c3c3930 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MirrorDecomposition/IsMonomialConjTranspose.lean#L97-L106

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MirrorDecomposition_IsMonomialConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.MirrorSection₂
open Formalism.FourierDecayAlt.C2
variable {m : ℕ}

theorem P2M_PI_MirrorSection__monomialMatrix_conjTranspose_6ef84c3c3930 (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) :
    (monoP w d)ᴴ = monoP w.symm (fun a => star (d (w.symm a))) := by sorry

alias «PI».«MirrorSection₂».«monomialMatrix_conjTranspose» := P2M_PI_MirrorSection__monomialMatrix_conjTranspose_6ef84c3c3930
