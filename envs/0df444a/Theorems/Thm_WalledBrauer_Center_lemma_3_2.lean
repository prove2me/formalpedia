-- Prove2me | Theorems.Thm_WalledBrauer_Center_lemma_3_2
-- name    : WalledBrauer.Center.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:01.374437+00:00
-- url     : https://prove2.me/theorems/aaf8aee9-1db0-442c-81c1-07f96d5ed54d
-- title:
--   Lemma 3.2 — relations of the Jucys–Murphy elements against $\tau_t$
-- statement:
--   For $1\le t\le\min(r,s)$ let $\tau_t=e_{r,r+1}e_{r-1,r+2}\cdots e_{r-t+1,r+t}\in B_{r,s}(\delta)$. Then
--
--   1. $(L_r+L_{r+1})\tau_t=(L_{r-1}+L_{r+2})\tau_t=\dots=(L_{r-t+1}+L_{r+t})\tau_t=0$, that is, $(L_a+L_{\tilde a})\tau_t=0$ for $r-t+1\le a\le r$, where $\tilde a=2r+1-a$;
--   2. for every $j\ge r+t+1$,
--   $$
--   \Bigl(-\sum_{i=r-t+1}^{r}e_{i,j}+\sum_{i=r+1}^{r+t}(i,j)\Bigr)\tau_t=0 .
--   $$
--
--   These relations let the Jucys–Murphy elements be pushed past the arcs of $\tau_t$ when computing their action on the cell module $C_{r,s}(\lambda)$ (Proposition 3.1).
--
--   **Formalization Note** Vertices are 0-based: $a$ runs over $r-t\le a<r$ with partner $2r-1-a$, and $j$ over $r+t\le j<r+s$; $\tau_t$ is `tau δ t`. The platform's product puts the left factor on top, the opposite of the paper's (p. 4). The relations are transcribed literally with the platform's product; each is the image of the page's relation under the up–down flip, an anti-automorphism fixing every $(a,b)$, $e_{i,j}$, $L_k$ and $\tau_t$, so it holds equally (in the paper's product it reads $\tau_t(L_a+L_{\tilde a})=0$).
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 14, Lemma 3.2, (3.1)

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem lemma_3_2 (r s : ℕ) (δ : ℂ) (t : ℕ) (ht : 1 ≤ t) (htr : t ≤ r) (hts : t ≤ s) :
    -- (1) `(L_a + L_{ã}) τ_t = 0`, `ã = 2r + 1 - a`, for `r - t + 1 ≤ a ≤ r` (0-based `a`, `2r - 1 - a`)
    (∀ (a : ℕ) (ha₁ : r - t ≤ a) (ha₂ : a < r),
        (jm δ ⟨a, by omega⟩ + jm δ ⟨2 * r - 1 - a, by omega⟩) * tau (r := r) (s := s) δ t = 0) ∧
    -- (2) `(-∑_{i=r-t+1}^{r} e_{i,j} + ∑_{i=r+1}^{r+t} (i, j)) τ_t = 0` for `j ≥ r + t + 1`
    (∀ j : Fin (r + s), r + t ≤ j.val →
        (-(∑ i ∈ Finset.univ.filter (fun i : Fin (r + s) => r - t ≤ i.val ∧ i.val < r), eArc δ i j)
          + ∑ i ∈ Finset.univ.filter (fun i : Fin (r + s) => r ≤ i.val ∧ i.val < r + t), tr δ i j)
          * tau (r := r) (s := s) δ t = 0) := by sorry
end WalledBrauer.Center
