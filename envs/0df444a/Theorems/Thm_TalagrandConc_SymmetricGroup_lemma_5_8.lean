-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_lemma_5_8
-- name    : TalagrandConc.SymmetricGroup.lemma_5_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:01.477526+00:00
-- url     : https://prove2.me/theorems/df68ea31-eda2-4d86-b994-6bc9e9ee2a6a
-- title:
--   Lemma 5.8 — for σ ∈ G'_i, f(A,σ,σ⁻¹(j),N+1) ≤ f(R'(A'_i), R'(σ), R'(σ)⁻¹(t_i(j)))
-- statement:
--   Let $A\subseteq S_{N+1}$, let $i,j\le N+1$ with $i\ne j$, and let $\sigma\in G'_i$, i.e. $\sigma(N+1)=i$. Let $t_i$ be the transposition of $N+1$ and $i$, and let $R'(\rho)=t_i\circ\rho$. Then $R'(\sigma)$ fixes $N+1$ and so lies in $S_N$, and $R'(A'_i)\subseteq S_N$ is the image of $A'_i=A\cap G'_i$. Since $j\ne i$, $t_i(j)\le N$, and
--   $$f\bigl(A,\sigma,\sigma^{-1}(j),N+1\bigr)\le f\bigl(R'(A'_i),R'(\sigma),R'(\sigma)^{-1}(t_i(j))\bigr).\tag{5.15}$$
--
--   This is the counterpart of Lemma 5.4 for left multiplication. It lets $(5.4)_N$ enter the proof of $(5.3)_{N+1}$.
--
--   **Formalization Note** $R'(\sigma)$ is passed as `R'σ : Perm (Fin N)` with `Restricts (t N i * σ) R'σ`. $t_i(j)$ is passed as `q : Fin N` with `q.castSucc = t N i j`. Both exist and are unique under the hypotheses.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 149, Lemma 5.8, Eq. (5.15)

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem lemma_5_8 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G' N i)
    (R'σ : Perm (Fin N)) (hR'σ : Restricts (t N i * σ) R'σ)
    (q : Fin N) (hq : q.castSucc = t N i j) :
    fpm A σ (σ⁻¹ j) (Fin.last N) ≤ fp (R'Image A i) R'σ (R'σ⁻¹ q) := by sorry
end TalagrandConc.SymmetricGroup
