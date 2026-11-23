-- Prove2me | Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_eq_filter__b757eed49bc8
-- name    : P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_eq_filter__b757eed49bc8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:37.64781+00:00
-- url     : https://prove2.me/theorems/3c0bff0f-801a-4335-a11b-67e5983718a3
-- title:
--   P2 M Formalism Irreducible Counting Lemmas Galois Irreducibility wt Of eq filter  b757eed49bc8: P2 M Formalism Irreducible Counting Lemmas Galois Irreducibility wt Of eq filter  b757eed49bc8
-- statement:
--   The P2 M Formalism Irreducible Counting Lemmas Galois Irreducibility wt Of eq filter  b757eed49bc8 construction uses the P2 M Formalism Irreducible Counting Lemmas Galois Irreducibility wt Of eq filter  b757eed49bc8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateIVOfTypeSetWeight.lean#L2199-L2206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/LocalEstimateIVOfTypeSetWeight.lean#L2199-L2206

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Polynomial
variable {α β : Type} [Fintype α]

theorem P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_eq_filter__b757eed49bc8 (μ : α → ℝ) (s : Finset α) (p : α → Prop) [DecidablePred p] :
    wtOf μ {x | x ∈ s ∧ p x} = ∑ x ∈ s.filter p, μ x := by sorry

alias «Formalism».«IrreducibleCountingLemmas».«GaloisIrreducibility».«wtOf_eq_filter'» := P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_eq_filter__b757eed49bc8
