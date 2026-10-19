-- Prove2me | Theorems.Thm_RobustSpecClust_Round_U0_isTopEigvecs
-- name    : RobustSpecClust.Round.U0_isTopEigvecs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:43:29.943089+00:00
-- url     : https://prove2.me/theorems/629ec764-3e0a-4ff6-abf2-46c45c9052b1
-- title:
--   Proof of Theorem 2, p. 46 — U⁰ = Z⁰Diag(1/√n_k) are top-r eigenvectors of X⁰ with eigenvalues n_k, and X⁰ vanishes on their complement
-- statement:
--   Let $\varphi : [n] \to [r]$ be a labelling with every cluster nonempty, $n_k = |\{i : \varphi(i) = k\}| > 0$. Let $X^0$ be the true clustering matrix ($X^0_{ij} = 1$ iff $\varphi(i)=\varphi(j)$) and $U^0 = Z^0\,\mathrm{Diag}(1/\sqrt{n_1},\dots,1/\sqrt{n_r})$. Then
--
--   1. the columns of $U^0$ are orthonormal top-$r$ eigenvectors of $X^0$, with eigenvalues the cluster sizes:
--   $$ (U^0)^\top U^0 = I_r, \qquad X^0 U^0 = U^0\,\mathrm{Diag}(n_1,\dots,n_r), $$
--   and $v^\top X^0 v \le n_k\, v^\top v$ for every $k$ and every $v \perp \mathrm{col}(U^0)$;
--   2. $X^0 v = 0$ for every $v$ orthogonal to the columns of $U^0$.
--
--   Together these say that the spectrum of $X^0$ is $n_1,\dots,n_r$ and then $0$, so the gap between the $r$-th and the $(r+1)$-th eigenvalue is $n_{\min}$: step (ii) of (G.6).
-- source:
--   arXiv:1912.07546v3, Appendix G, proof of Theorem 2, p. 46, first paragraph (U⁰ = Z⁰ Diag(1/√n₁, …, 1/√n_r)) and (G.6)(ii)

import Mathlib
import Definitions.Def_RobustSpecClust_Round_Setting

namespace RobustSpecClust.Round

open Matrix

theorem U0_isTopEigvecs {n r : ℕ} (φ : Fin n → Fin r) (hφ : ∀ k, 0 < clusterSize φ k) :
    IsTopEigvecsWith (trueClust φ) (U0 φ) (fun k => (clusterSize φ k : ℝ)) ∧
      ∀ v : Fin n → ℝ, (U0 φ)ᵀ *ᵥ v = 0 → trueClust φ *ᵥ v = 0 := by sorry

end RobustSpecClust.Round
