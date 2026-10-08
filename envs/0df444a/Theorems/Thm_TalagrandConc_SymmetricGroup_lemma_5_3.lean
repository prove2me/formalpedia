-- Prove2me | Theorems.Thm_TalagrandConc_SymmetricGroup_lemma_5_3
-- name    : TalagrandConc.SymmetricGroup.lemma_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:38.170232+00:00
-- url     : https://prove2.me/theorems/3a9284ff-618a-4194-812e-09a65083aa1d
-- title:
--   Lemma 5.3 — f(A,σ,i) ≤ 4(1−λ)² + (1−λ) g(A,σ,i,j) + λ f(A,σ,j,i)
-- statement:
--   Let $A\subseteq S_{N+1}$, let $\sigma\in S_{N+1}$, let $i,j\le N+1$ with $i\ne j$, and let $0\le\lambda\le1$. With the convex-distance functionals $f(A,\sigma,i)$, $g(A,\sigma,i,j)$ and $f(A,\sigma,j,i)$ of Chapter 5 (Eqs. (5.5)–(5.6)),
--   $$f(A,\sigma,i)\le 4(1-\lambda)^2+(1-\lambda)\,g(A,\sigma,i,j)+\lambda\,f(A,\sigma,j,i).\tag{5.7}$$
--
--   This is a deterministic inequality. It plays the role in the symmetric group that the one-coordinate interpolation plays in the proof of Theorem 4.1.1, and it is combined with Hölder's inequality in the induction step for $(5.4)_{N+1}$.
--
--   **Formalization Note** The functionals take values in $[0,+\infty]$ with $0\cdot(+\infty)=0$. So for $\lambda=0$ the last term vanishes even when the face $\{s\in V_A(\sigma): s_i=0\}$ is empty.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 146, Lemma 5.3, Eq. (5.7)

import Mathlib
import Definitions.Def_TalagrandConc_SymmetricGroup_Basic

namespace TalagrandConc.SymmetricGroup

open scoped ENNReal
open Equiv

theorem lemma_5_3 {N : ℕ} (A : Set (Perm (Fin (N + 1)))) (i j : Fin (N + 1))
    (hij : i ≠ j) (σ : Perm (Fin (N + 1))) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    fp A σ i ≤ ENNReal.ofReal (4 * (1 - lam) ^ 2) + ENNReal.ofReal (1 - lam) * g A σ i j
      + ENNReal.ofReal lam * fpm A σ j i := by sorry
end TalagrandConc.SymmetricGroup
