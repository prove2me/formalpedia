-- Prove2me | Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_e3__nonneg_6e96a0337fe1
-- name    : P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_e3__nonneg_6e96a0337fe1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:52.134993+00:00
-- url     : https://prove2.me/theorems/b7e69a6d-86d0-4b6b-8eb6-7f61ce01f438
-- title:
--   P2 M Formalism Irreducible Counting Lemmas Galois Irreducibility e3  nonneg 6e96a0337fe1: P2 M Formalism Irreducible Counting Lemmas Galois Irreducibility e3  nonneg 6e96a0337fe1
-- statement:
--   The P2 M Formalism Irreducible Counting Lemmas Galois Irreducibility e3  nonneg 6e96a0337fe1 construction uses the P2 M Formalism Irreducible Counting Lemmas Galois Irreducibility e3  nonneg 6e96a0337fe1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L83-L85

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]

theorem P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_e3__nonneg_6e96a0337fe1 (N : ℕ) (c : Fin N → K) : 0 ≤ e3μ K N c := by sorry

alias «Formalism».«IrreducibleCountingLemmas».«GaloisIrreducibility».«e3μ_nonneg» := P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_e3__nonneg_6e96a0337fe1
