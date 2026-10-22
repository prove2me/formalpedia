-- Prove2me | Theorems.Thm_WalledBrauer_Center_lemma_2_12
-- name    : WalledBrauer.Center.lemma_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:29.553793+00:00
-- url     : https://prove2.me/theorems/eaa39d1e-7785-4b7a-b3c2-ec4b70d96f76
-- title:
--   Lemma 2.12 — supersymmetric polynomials separate the content vectors $c(\lambda,\cdot)$ in the semisimple case
-- statement:
--   Assume that $B_{r,s}(\delta)$ is semisimple. If $\lambda\ne\mu$ are elements of $\Lambda_{r,s}$ (bipartitions $(\lambda^L,\lambda^R)$ with $|\lambda^L|=r-t$, $|\lambda^R|=s-t$ for some $0\le t\le\min(r,s)$), then there is a supersymmetric polynomial $p^{\lambda,\mu}$ with
--
--   $$
--   p^{\lambda,\mu}\bigl((c(\lambda,i))_{1\le i\le r+s}\bigr)\ne p^{\lambda,\mu}\bigl((c(\mu,i))_{1\le i\le r+s}\bigr),
--   $$
--
--   where $c(\lambda,i)$ is the content vector of p. 12. Since supersymmetric polynomials in the $L_k$ act on the cell module $C_{r,s}(\lambda)$ by the scalar $p(c(\lambda,\cdot))$ (Corollary 3.3), this lemma is what distinguishes the cell modules by central elements.
--
--   **Formalization Note** $\Lambda_{r,s}$ is the published `CellIndex r s` (the triple $(t,\lambda^L,\lambda^R)$); $c(\lambda,\cdot)$ is `cVec δ λ`, the point indexed like the variables $x_1,\dots,x_r,y_1,\dots,y_s$. Semisimplicity is `IsSemisimpleRing`.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 12, Lemma 2.12

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem lemma_2_12 (r s : ℕ) (δ : ℂ) (hss : IsSemisimpleRing (B r s δ))
    (x y : CellIndex r s) (hxy : x ≠ y) :
    ∃ p : MvPolynomial (Fin r ⊕ Fin s) ℂ,
      IsSupersymmetric p ∧ eval (cVec δ x) p ≠ eval (cVec δ y) p := by sorry
end WalledBrauer.Center
