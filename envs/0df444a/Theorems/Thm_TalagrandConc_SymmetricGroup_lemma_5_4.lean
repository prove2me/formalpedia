-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_lemma_5_4
-- name    : TalagrandConc.SymmetricGroup.lemma_5_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:49.320974+00:00
-- url     : https://prove2.me/theorems/844b6cd9-56c0-4297-aa23-a08e43da700a
-- title:
--   Lemma 5.4 — for σ ∈ G_i, f(A,σ,j,i) ≤ f(R(A_i), R(σ), t_i(j))
-- statement:
--   Let $A\subseteq S_{N+1}$, let $i,j\le N+1$ with $i\ne j$, and let $\sigma\in G_i$, i.e. $\sigma(i)=N+1$. Let $t_i$ be the transposition of $N+1$ and $i$, and let $R(\rho)=\rho\circ t_i$. Then $R(\sigma)$ fixes $N+1$ and so lies in $S_N$, and $R(A_i)\subseteq S_N$ is the image of $A_i=A\cap G_i$. Since $j\ne i$, $t_i(j)\le N$, and
--   $$f(A,\sigma,j,i)\le f\bigl(R(A_i),R(\sigma),t_i(j)\bigr).\tag{5.8}$$
--
--   This deterministic comparison transfers the face functional on $S_{N+1}$ to the functional $f(\cdot,\cdot,p)$ on $S_N$. It is what lets the induction hypothesis $(5.3)_N$ enter the proof of $(5.4)_{N+1}$.
--
--   **Formalization Note** $R(\sigma)$ is passed as a permutation `Rσ` of `Fin N` together with the hypothesis `Restricts (σ * t N i) Rσ`, which says that $(\sigma\circ t_i)(\ell)=R(\sigma)(\ell)$ for every $\ell\le N$. Likewise $t_i(j)$ is passed as `q : Fin N` with `q.castSucc = t N i j`. Both objects exist and are unique under the hypotheses.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 147, Lemma 5.4, Eq. (5.8)

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem lemma_5_4 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (hσ : σ ∈ G N i)
    (Rσ : Perm (Fin N)) (hRσ : Restricts (σ * t N i) Rσ)
    (q : Fin N) (hq : q.castSucc = t N i j) :
    fpm A σ j i ≤ fp (RImage A i) Rσ q := by sorry
end TalagrandConc.SymmetricGroup
