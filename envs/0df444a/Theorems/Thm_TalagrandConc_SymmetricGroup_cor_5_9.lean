-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_cor_5_9
-- name    : TalagrandConc.SymmetricGroup.cor_5_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:10.812985+00:00
-- url     : https://prove2.me/theorems/0db7fe19-e786-43d1-841b-7bada73c14ad
-- title:
--   Corollary 5.9 — assuming (5.4)_N, ∫ exp(f(A,σ,σ⁻¹(j),N+1)/16) dQ'_i ≤ 1/Q'_i(A)
-- statement:
--   Assume the induction hypothesis $(5.4)_N$: for every $B\subseteq S_N$ and every $p\le N$, $\int_{S_N}\exp\frac1{16}f(B,\rho,\rho^{-1}(p))\,dP_N(\rho)\le1/P_N(B)$. Let $A\subseteq S_{N+1}$ and $i,j\le N+1$ with $j\ne i$. Let $Q'_i$ be the uniform probability on $G'_i=\{\sigma\in S_{N+1}:\sigma(N+1)=i\}$. Then
--   $$\int\exp\frac1{16}f\bigl(A,\sigma,\sigma^{-1}(j),N+1\bigr)\,dQ'_i(\sigma)\le\frac1{Q'_i(A)}.\tag{5.16}$$
--
--   This bound enters the induction step for $(5.3)_{N+1}$, and it is where the two inequalities of Proposition 5.2 cross: $(5.3)_{N+1}$ needs $(5.4)_N$.
--
--   **Formalization Note** The hypothesis $(5.4)_N$ is an explicit binder (`Ineq54 N`). $Q'_i(A)=|A\cap G'_i|/|G'_i|$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 150, Corollary 5.9, Eq. (5.16)

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem cor_5_9 {N : ℕ} (hIH : Ineq54 N) (A : Set (Perm (Fin (N + 1))))
    (i j : Fin (N + 1)) (hji : j ≠ i) :
    uniformAvg (G' N i) (fun σ => exp16 (fpm A σ (σ⁻¹ j) (Fin.last N)))
      ≤ (uniformProb (G' N i) A)⁻¹ := by sorry
end TalagrandConc.SymmetricGroup
