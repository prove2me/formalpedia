-- Prove2me | Theorems.Thm_SPP_eq_mul_mul_of_carmichael
-- name    : SPP.eq_mul_mul_of_carmichael
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:10:02.859103+00:00
-- url     : https://prove2.me/theorems/68583db6-2270-43b4-9866-8cf6d71d0251
-- title:
--   SPP: eq mul mul of carmichael
-- statement:
--   The SPP construction uses the eq mul mul of carmichael property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L561-L588
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L561-L588

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
set_option autoImplicit false
open Nat
open SPP
open Subgroup
variable {n : ℕ}

theorem SPP.eq_mul_mul_of_carmichael [hn : Fact (1 < n)] (hc : FPP.Carmichael n) (hnp : ¬n.Prime) :
    ∃ m₁ m₂ m₃, n = m₁ * m₂ * m₃ ∧ m₁.Coprime m₂ ∧ m₁.Coprime m₃ ∧ m₂.Coprime m₃ ∧
      2 < m₁ ∧ 2 < m₂ ∧ 2 < m₃ := by sorry
