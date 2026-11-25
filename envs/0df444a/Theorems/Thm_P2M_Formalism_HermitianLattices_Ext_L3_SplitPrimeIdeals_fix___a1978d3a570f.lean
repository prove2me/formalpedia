-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_fix___a1978d3a570f
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_fix___a1978d3a570f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:49.940252+00:00
-- url     : https://prove2.me/theorems/e1ca325f-abf6-41a9-b806-523a45b4703d
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Split Prime Ideals fix   a1978d3a570f: P2 M Formalism Hermitian Lattices Ext L3 Split Prime Ideals fix   a1978d3a570f
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Split Prime Ideals fix   a1978d3a570f construction uses the P2 M Formalism Hermitian Lattices Ext L3 Split Prime Ideals fix   a1978d3a570f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L37-L38

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVariant_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NotIsPrimeMapOfSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SplitPrimeIdeals
variable {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} {σ : B →+* B}

theorem P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_fix___a1978d3a570f (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (a : A) : σ (ι a) = ι a := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«SplitPrimeIdeals».«fix_ι» := P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_fix___a1978d3a570f
