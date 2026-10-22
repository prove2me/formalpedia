-- Prove2me | Theorems.Thm_WalledBrauer_Center_proposition_2_4
-- name    : WalledBrauer.Center.proposition_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:02.391754+00:00
-- url     : https://prove2.me/theorems/329d3666-d011-46ad-b5ee-1b34a8b09ef8
-- title:
--   Proposition 2.4 — relations between $L_k$ and the generators $(i,i+1)$, $e_{r,r+1}$
-- statement:
--   Let $L_1,\dots,L_{r+s}$ be the Jucys–Murphy elements of $B_{r,s}(\delta)$. Then:
--
--   1. $(i,i+1)L_{i+1}-L_i(i,i+1)=1$ for $i\ne r$;
--   2. $L_{i+1}(i,i+1)-(i,i+1)L_i=1$ for $i\ne r$;
--   3. $e_{r,r+1}(L_r+L_{r+1})=(L_r+L_{r+1})e_{r,r+1}=0$;
--   4. $(i,i+1)L_k=L_k(i,i+1)$ for $k\ne i,i+1$;
--   5. $e_{r,r+1}L_k=L_ke_{r,r+1}$ for $k\ne r,r+1$.
--
--   Here $1\le i\le r+s-1$, $i\ne r$, so that $(i,i+1)$ is a transposition on one side of the wall, and (3), (5) concern $r,s\ge1$. These are the walled analogues of the degenerate affine Hecke relations and give the commutativity of the $L_k$ and the centrality of the power sums in them.
--
--   **Formalization Note** Vertices are 0-based: the paper's $i$ is the Lean `i + 1`, and "$i\ne r$" is written as `i + 1 < r ∨ r ≤ i` (both $i$ and $i+1$ on one side), avoiding natural-number subtraction. $e_{r,r+1}$ is `eArc` at the 0-based vertices $r-1$, $r$, under $0<r$, $0<s$. The platform's product puts the left factor on top, the opposite of the paper's (p. 4). The relations are transcribed literally with the platform's product; each is the image of a relation of the paper under the up–down flip, an anti-automorphism fixing every $(a,b)$, $e_{j,k}$ and $L_k$, so it holds equally (for instance, (1) transcribed is the paper's (2)).
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 8, Proposition 2.4

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem proposition_2_4 (r s : ℕ) (δ : ℂ) :
    -- (1) `(i, i+1) L_{i+1} - L_i (i, i+1) = 1` for `i ≠ r` (0-based `i`, `i+1` on one side)
    (∀ (i : ℕ) (hi : i + 1 < r + s), (i + 1 < r ∨ r ≤ i) →
        tr δ ⟨i, by omega⟩ ⟨i + 1, hi⟩ * jm δ ⟨i + 1, hi⟩ -
          jm δ ⟨i, by omega⟩ * tr δ ⟨i, by omega⟩ ⟨i + 1, hi⟩ = 1) ∧
    -- (2) `L_{i+1} (i, i+1) - (i, i+1) L_i = 1` for `i ≠ r`
    (∀ (i : ℕ) (hi : i + 1 < r + s), (i + 1 < r ∨ r ≤ i) →
        jm δ ⟨i + 1, hi⟩ * tr δ ⟨i, by omega⟩ ⟨i + 1, hi⟩ -
          tr δ ⟨i, by omega⟩ ⟨i + 1, hi⟩ * jm δ ⟨i, by omega⟩ = 1) ∧
    -- (3) `e_{r,r+1} (L_r + L_{r+1}) = (L_r + L_{r+1}) e_{r,r+1} = 0`
    (∀ (hr : 0 < r) (hs : 0 < s),
        eArc δ (⟨r - 1, by omega⟩ : Fin (r + s)) (⟨r, by omega⟩ : Fin (r + s)) * (jm δ (⟨r - 1, by omega⟩ : Fin (r + s)) + jm δ (⟨r, by omega⟩ : Fin (r + s))) = 0 ∧
        (jm δ (⟨r - 1, by omega⟩ : Fin (r + s)) + jm δ (⟨r, by omega⟩ : Fin (r + s))) * eArc δ (⟨r - 1, by omega⟩ : Fin (r + s)) (⟨r, by omega⟩ : Fin (r + s)) = 0) ∧
    -- (4) `(i, i+1) L_k = L_k (i, i+1)` for `k ≠ i, i+1`
    (∀ (i : ℕ) (hi : i + 1 < r + s), (i + 1 < r ∨ r ≤ i) → ∀ k : Fin (r + s),
        k.val ≠ i → k.val ≠ i + 1 →
        tr δ ⟨i, by omega⟩ ⟨i + 1, hi⟩ * jm δ k = jm δ k * tr δ ⟨i, by omega⟩ ⟨i + 1, hi⟩) ∧
    -- (5) `e_{r,r+1} L_k = L_k e_{r,r+1}` for `k ≠ r, r+1`
    (∀ (hr : 0 < r) (hs : 0 < s) (k : Fin (r + s)), k.val ≠ r - 1 → k.val ≠ r →
        eArc δ (⟨r - 1, by omega⟩ : Fin (r + s)) (⟨r, by omega⟩ : Fin (r + s)) * jm δ k =
          jm δ k * eArc δ (⟨r - 1, by omega⟩ : Fin (r + s)) (⟨r, by omega⟩ : Fin (r + s))) := by sorry
end WalledBrauer.Center
