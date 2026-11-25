-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap___comap_ebbf3c779431
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap___comap_ebbf3c779431
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:50.627724+00:00
-- url     : https://prove2.me/theorems/eeb1e15d-caae-428b-b14f-ae9afc7a258e
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Split Prime Ideals comap   comap ebbf3c779431: P2 M Formalism Hermitian Lattices Ext L3 Split Prime Ideals comap   comap ebbf3c779431
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Split Prime Ideals comap   comap ebbf3c779431 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Split Prime Ideals comap   comap ebbf3c779431 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NotIsPrimeMapOfSplit.lean#L40-L43

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap___comap_ebbf3c779431 (hfix : ∀ x, σ x = x ↔ x ∈ Set.range ι) (P : Ideal B) :
    (P.comap σ).comap ι = P.comap ι := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«SplitPrimeIdeals».«comap_ι_comap» := P2M_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap___comap_ebbf3c779431
