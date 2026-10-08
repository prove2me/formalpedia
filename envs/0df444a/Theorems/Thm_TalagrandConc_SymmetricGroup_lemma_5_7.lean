-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_lemma_5_7
-- name    : TalagrandConc.SymmetricGroup.lemma_5_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:58.151728+00:00
-- url     : https://prove2.me/theorems/bb5294ed-b1e3-4aa4-8063-e0eff150f638
-- title:
--   Lemma 5.7 — f(A,σ,N+1) ≤ 4(1−λ)² + (1−λ) g(A,σ,N+1,σ⁻¹(j)) + λ f(A,σ,σ⁻¹(j),N+1)
-- statement:
--   Let $A\subseteq S_{N+1}$, let $\sigma\in S_{N+1}$, let $j\le N+1$ with $j\ne\sigma(N+1)$, and let $0\le\lambda\le1$. Then
--   $$f(A,\sigma,N+1)\le4(1-\lambda)^2+(1-\lambda)\,g\bigl(A,\sigma,N+1,\sigma^{-1}(j)\bigr)+\lambda\,f\bigl(A,\sigma,\sigma^{-1}(j),N+1\bigr).\tag{5.14}$$
--
--   This is the deterministic inequality that starts the proof of $(5.3)_{N+1}$. The paper obtains it from (5.7) by replacing $i$ with $N+1$ and $j$ with $\sigma^{-1}(j)$.
--
--   **Formalization Note** $N+1$ is `Fin.last N`. The functionals take values in $[0,+\infty]$ with $0\cdot(+\infty)=0$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 149, Lemma 5.7, Eq. (5.14)

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem lemma_5_7 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (σ : Perm (Fin (N + 1)))
    (j : Fin (N + 1)) (hj : j ≠ σ (Fin.last N)) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fp A σ (Fin.last N) ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2)
      + ENNReal.ofReal (1 - lam) * g A σ (Fin.last N) (σ⁻¹ j)
      + ENNReal.ofReal lam * fpm A σ (σ⁻¹ j) (Fin.last N) := by sorry
end TalagrandConc.SymmetricGroup
