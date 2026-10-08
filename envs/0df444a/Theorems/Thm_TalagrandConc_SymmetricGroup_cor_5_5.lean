-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_cor_5_5
-- name    : TalagrandConc.SymmetricGroup.cor_5_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:45.075462+00:00
-- url     : https://prove2.me/theorems/f66f79d2-75c4-4211-8a63-b523f7ec5f53
-- title:
--   Corollary 5.5 — assuming (5.3)_N, ∫ exp(f(A,σ,j,i)/16) dQ_i ≤ 1/Q_i(A)
-- statement:
--   Assume the induction hypothesis $(5.3)_N$: for every $B\subseteq S_N$ and every $p\le N$, $\int_{S_N}\exp\frac1{16}f(B,\rho,p)\,dP_N(\rho)\le 1/P_N(B)$. Let $A\subseteq S_{N+1}$ and $i,j\le N+1$ with $i\ne j$. Let $Q_i$ be the uniform probability on $G_i=\{\sigma\in S_{N+1}:\sigma(i)=N+1\}$. Then
--   $$\int\exp\frac1{16}f(A,\sigma,j,i)\,dQ_i(\sigma)\le\frac1{Q_i(A_i)}=\frac1{Q_i(A)}.\tag{5.10}$$
--
--   This is one of the two integral bounds that Hölder's inequality combines in the induction step for $(5.4)_{N+1}$.
--
--   **Formalization Note** The paper states this inside the proof of Proposition 5.2, for a subset of $S_{N+1}$ at the induction step. The hypothesis $(5.3)_N$ is therefore an explicit binder (`Ineq53 N`). $Q_i(A)$ means $Q_i(A\cap G_i)=|A\cap G_i|/|G_i|$. If $A\cap G_i=\emptyset$, the right-hand side is $+\infty$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 147, Corollary 5.5, Eq. (5.10)

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem cor_5_5 {N : ℕ} (hIH : Ineq53 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hij : i ≠ j) :
    uniformAvg (G N i) (fun σ => exp16 (fpm A σ j i)) ≤ (uniformProb (G N i) A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup
