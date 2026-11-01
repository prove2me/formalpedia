-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch17_triangularMod5_range
-- name    : QseriesFormalization.PartIV.Ch17.triangularMod5_range
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:45:28.212104+00:00
-- url     : https://prove2.me/theorems/8e12a582-a8b3-4deb-b65e-455a6e41746a
-- title:
--   Triangular residues mod 5 lie in $\{0,1,3\}$
-- statement:
--   Define `triangularMod5` on $\mathbb{Z}/5$ by $k\mapsto 3k(k+1)$ (this is $k(k+1)/2$ computed using $2^{-1}=3$ in $\mathbb{Z}/5$). The statement: for every $k\in\mathbb{Z}/5$,
--   $$3k(k+1)\in\{0,1,3\}\subset\mathbb{Z}/5.$$
--   It is a finite residue check in Chapter 17's mod 5 proof of Ramanujan's congruence.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 17. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter17_Mod5ResidueAnalysis.lean#L37-L41

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

theorem QseriesFormalization.PartIV.Ch17.triangularMod5_range : ∀ k : ZMod 5,
    triangularMod5 k = 0 ∨ triangularMod5 k = 1 ∨ triangularMod5 k = 3 := by sorry
