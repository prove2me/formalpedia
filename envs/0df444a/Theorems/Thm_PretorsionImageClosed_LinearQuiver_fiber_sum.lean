-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_fiber_sum
-- name    : PretorsionImageClosed.LinearQuiver.fiber_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T06:47:16.547095+00:00
-- url     : https://prove2.me/theorems/6cbb30ef-a636-443c-9fa0-797745af160f
-- title:
--   Linear Quiver: fiber sum
-- statement:
--   Lemma 7.3: the weights of the extensions of `p` sum to `q^{|ind(T ∩ F)|} · psi (candRows p)`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L437-L499
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean#L437-L499

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open Statement Polynomial Finset
open PretorsionImageClosed.LinearQuiver
variable {n : ℕ}

theorem PretorsionImageClosed.LinearQuiver.fiber_sum (p : CutoffPair n) :
    ∑ x ∈ univ.filter (fun x : CutoffPair (n + 1) => x.restrict = p), cpWeight x =
      C (q ^ middleCount p.1.1 p.1.2) * psi (candRows p) := by sorry
