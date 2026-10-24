-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_triangular_plus_pentagonal_ne_four
-- name    : QseriesFormalization.PartIV.Ch17.triangular_plus_pentagonal_ne_four
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:46:33.903019+00:00
-- url     : https://prove2.me/theorems/f20e4434-a3d5-4ee5-993a-996163f68f78
-- title:
--   Residue obstruction: triangular + pentagonal $\not\equiv4 \pmod 5$
-- statement:
--   Let $k,j\in\mathbb{Z}/5$ with $2k+1\neq0$. Then
--   $$3k(k+1)+3j(3j+1)\neq 4\ \text{ in }\mathbb{Z}/5,$$
--   i.e. triangular residue plus (plus-side) pentagonal residue (`triangularMod5`, `pentagonalMod5`) is never $4$. This is the key obstruction in Chapter 17's proof that the coefficient of $q^{5n+4}$ in the relevant product vanishes mod 5.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_Mod5ResidueAnalysis.lean#L62-L74

import Definitions.Def_QseriesFormalization_Chapter17_Mod5ResidueAnalysis
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

open QseriesFormalization
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch17

open ZMod

theorem QseriesFormalization.PartIV.Ch17.triangular_plus_pentagonal_ne_four
    (k j : ZMod 5) (hk : (2 * k + 1 : ZMod 5) ≠ 0) :
    triangularMod5 k + pentagonalMod5 j ≠ 4 := by sorry
