-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_square__272802dadd0c
-- name    : P2M_FixedOrderFactor_sum_orbitAvg_square__272802dadd0c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:00.175807+00:00
-- url     : https://prove2.me/theorems/db927c4f-38d3-4ed6-846c-5bbf6f38dd74
-- title:
--   P2 M Fixed Order Factor sum orbit Avg square  272802dadd0c: P2 M Fixed Order Factor sum orbit Avg square  272802dadd0c
-- statement:
--   **The prime-square term.** For `M > 0` and `s ∣ M`, the squares `(t, y)² = ((1 + y)t, y²)` of
--   the elements of `ℤ/s ⋊ (ℤ/M)ˣ` lying over `a` give
--   `∑_{y ∈ (ℤ/M)ˣ, y² = a} ∑_{t<s} ϱ_s((ȳ + 1)t) = s · β(M, a, s)`, where `ȳ ∈ ℤ/s` is the image of `y`
--   (taken through its least nonnegative representative) and `β(M, a, s)` is the number of residue
--   classes `y` with `y² = a` and `ȳ = -1`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L150-L164
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L150-L164

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
variable {M : ℕ} [NeZero M]

theorem P2M_FixedOrderFactor_sum_orbitAvg_square__272802dadd0c {s : ℕ} (hs : s ∣ M) (a : ℕ) :
    ∑ y ∈ univ.filter (fun y : ZMod M => IsUnit y ∧ y ^ 2 = a),
      ∑ t ∈ range s, orbitAvg s (((ZMod.castHom hs (ZMod s) y).val + 1) * t) =
      s * sqrtCount M a s := by sorry

alias «FixedOrderFactor».«sum_orbitAvg_square'» := P2M_FixedOrderFactor_sum_orbitAvg_square__272802dadd0c
