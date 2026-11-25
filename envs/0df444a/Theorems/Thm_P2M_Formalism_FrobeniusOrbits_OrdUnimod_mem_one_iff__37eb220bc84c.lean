-- Prove2me | Theorems.Thm_P2M_Formalism_FrobeniusOrbits_OrdUnimod_mem_one_iff__37eb220bc84c
-- name    : P2M_Formalism_FrobeniusOrbits_OrdUnimod_mem_one_iff__37eb220bc84c
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:56:35.948967+00:00
-- url     : https://prove2.me/theorems/9568daff-1b85-4312-870c-a7b2eece3e6d
-- title:
--   P2 M Formalism Frobenius Orbits Ord Unimod mem one iff  37eb220bc84c: P2 M Formalism Frobenius Orbits Ord Unimod mem one iff  37eb220bc84c
-- statement:
--   The P2 M Formalism Frobenius Orbits Ord Unimod mem one iff  37eb220bc84c construction uses the P2 M Formalism Frobenius Orbits Ord Unimod mem one iff  37eb220bc84c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrdUnimod.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrdUnimod.lean#L22-L24

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrdUnimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.OrdUnimod
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem P2M_Formalism_FrobeniusOrbits_OrdUnimod_mem_one_iff__37eb220bc84c (t : hostE ζ a b) :
    t ∈ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ↔ IsIntegral ℤ t := by sorry

alias «Formalism».«FrobeniusOrbits».«OrdUnimod».«mem_one_iff'» := P2M_Formalism_FrobeniusOrbits_OrdUnimod_mem_one_iff__37eb220bc84c
