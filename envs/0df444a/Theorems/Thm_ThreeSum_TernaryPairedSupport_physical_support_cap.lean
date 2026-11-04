-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedSupport_physical_support_cap
-- name    : ThreeSum.TernaryPairedSupport.physical_support_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:57.797788+00:00
-- url     : https://prove2.me/theorems/90cd535e-4c85-4265-a88c-3618f33ad042
-- title:
--   Ternary Paired Support: physical support cap
-- statement:
--   One representative per physical mode is enough. The two injectivity
--   premises are stated on the actual original pair records, not on local words.
--   In particular the left-hash premise needs singleton ORIGINAL source buckets.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L165-L199
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupport.lean#L165-L199

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

theorem ThreeSum.TernaryPairedSupport.physical_support_cap (L R : P → V) (H : V →ₗ[K] W) (o : W)
    (mode : P → D) (m : ℕ)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : ∀ a b, L a+R a=L b+R b → mode a=mode b)
    (hhash : ∀ a b, H (L a)=H (L b) → mode a=mode b)
    (hno : ∀ e : Fin m → P,
      ¬ LinearIndependent K (taggedEndpoints (K := K) (L ∘ e) (R ∘ e))) :
    (physicalSupport mode).card ≤ 2 * Fintype.card K ^ m := by sorry
