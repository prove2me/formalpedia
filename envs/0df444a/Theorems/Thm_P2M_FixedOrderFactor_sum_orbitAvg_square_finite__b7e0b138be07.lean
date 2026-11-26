-- Prove2me | Theorems.Thm_P2M_FixedOrderFactor_sum_orbitAvg_square_finite__b7e0b138be07
-- name    : P2M_FixedOrderFactor_sum_orbitAvg_square_finite__b7e0b138be07
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:30.117009+00:00
-- url     : https://prove2.me/theorems/c8e7af8c-e3c3-5f3c-944d-0ce4e4a4d221
-- title:
--   P2 M Fixed Order Factor sum orbit Avg square finite  b7e0b138be07: P2 M Fixed Order Factor sum orbit Avg square finite  b7e0b138be07
-- statement:
--   **The finite-sum identity** behind the prime-square term, over the representatives
--   `0 ≤ x < M`, for all `M` and `s > 0`: `∑_{x² ≡ a} ∑_{t<s} ϱ_s((x + 1)t) = s · β(M, a, s)`. It is
--   vacuous at `M = 0`, and for `s ∤ M` it is an identity of arithmetic counts, not of residue classes;
--   the group-theoretic reading is `sum_orbitAvg_square'`, under `M > 0` and `s ∣ M`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L93-L98
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L93-L98

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor

theorem P2M_FixedOrderFactor_sum_orbitAvg_square_finite__b7e0b138be07 {s : ℕ} (hs : 0 < s) (M a : ℕ) :
    ∑ x ∈ (range M).filter (fun x => Nat.Coprime x M ∧ x ^ 2 % M = a % M),
      ∑ t ∈ range s, orbitAvg s ((x + 1) * t) = s * sqrtCount M a s := by sorry

alias «FixedOrderFactor».«sum_orbitAvg_square_finite'» := P2M_FixedOrderFactor_sum_orbitAvg_square_finite__b7e0b138be07
