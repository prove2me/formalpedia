-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupport_physical_support_cap_of_zero_potential
-- name    : ThreeSum.TernaryPairedSupport.physical_support_cap_of_zero_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:43:01.577611+00:00
-- url     : https://prove2.me/theorems/cf283929-1645-4921-8792-1e962cee44f7
-- title:
--   Ternary Paired Support: physical support cap of zero potential
-- statement:
--   A zero nonnegative tuple potential supplies the no-full-rank premise.
--   The caller must prove the actual full-rank tuple gives positive weight;
--   the theorem does not substitute a marginal score for the paired potential.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L204-L220
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L204-L220

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupport
open Finset
attribute [local instance] Classical.propDecidable
variable {K E V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
  [AddCommGroup W] [Module K W] [Fintype W]
  [Fintype E]
variable {P D : Type*} [Fintype P] [DecidableEq D]

theorem ThreeSum.TernaryPairedSupport.physical_support_cap_of_zero_potential
    (L R : P → V) (H : V →ₗ[K] W) (o : W) (mode : P → D) (m : ℕ)
    (weight : (Fin m → P) → ℕ)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : ∀ a b, L a+R a=L b+R b → mode a=mode b)
    (hhash : ∀ a b, H (L a)=H (L b) → mode a=mode b)
    (hpos : ∀ e, LinearIndependent K
      (taggedEndpoints (K := K) (L ∘ e) (R ∘ e)) → 0 < weight e)
    (hzero : (∑ e : Fin m → P, weight e)=0) :
    (physicalSupport mode).card ≤ 2 * Fintype.card K ^ m := by sorry
