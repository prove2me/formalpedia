-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_jacobi_coeff_zero_iff
-- name    : QseriesFormalization.PartIV.Ch17.jacobi_coeff_zero_iff
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:35:10.013416+00:00
-- url     : https://prove2.me/theorems/9f97ec60-d89d-41cc-bbe9-ea452edb4fd6
-- title:
--   In $\mathbb{Z}/5$, $2k+1=0$ exactly when $k=2$
-- statement:
--   For every $k\in\mathbb{Z}/5$,
--   $$2k+1=0\iff k=2.$$
--   This identifies which residues of the triangular index make the Jacobi coefficient $2k+1$ vanish mod 5 in Chapter 17.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_Mod5ResidueAnalysis.lean#L49-L51

import Mathlib.Data.ZMod.Basic

/-!
# Chapter 17 — Ramanujan-Watson mod-5 residue analysis

Key combinatorial facts at the heart of Ramanujan's 1919 proof of
`∀ n, 5 ∣ p(5n+4)`.  Working in `ZMod 5` (where 2 is invertible with
inverse 3), the triangular and pentagonal exponents become:

  - **Triangular** `T_k = k(k+1)/2`; in ZMod 5: `3·k·(k+1)`.
    Range: `{0, 1, 3} ⊂ ZMod 5`.
  - **Pentagonal** `P_j = j(3j+1)/2`; in ZMod 5: `3·j·(3j+1)`.
    Range: `{0, 1, 2} ⊂ ZMod 5`.

The Jacobi coefficient `2k+1` vanishes in ZMod 5 exactly when `k ≡ 2`,
which is exactly when `T_k ≡ 3` (mod 5).  So contributing pairs have
`T_k ∈ {0, 1}` and `P_j ∈ {0, 1, 2}`, giving `T_k + P_j ∈ {0,1,2,3}` —
**never 4**.

This file proves the enumeration facts by `decide` on `Fin 5` / `ZMod 5`.
-/

open ZMod

theorem QseriesFormalization.PartIV.Ch17.jacobi_coeff_zero_iff : ∀ k : ZMod 5,
    (2 * k + 1 : ZMod 5) = 0 ↔ k = 2 := by sorry
