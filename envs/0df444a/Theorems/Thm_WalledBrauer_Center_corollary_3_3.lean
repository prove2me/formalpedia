-- Prove2me | Theorems.Thm_WalledBrauer_Center_corollary_3_3
-- name    : WalledBrauer.Center.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:01.857697+00:00
-- url     : https://prove2.me/theorems/e915ae7d-a284-46e5-ac56-8f8de7aa4474
-- title:
--   Corollary 3.3 — $f(L_1,\dots,L_{r+s})$ acts on $C_{r,s}(\lambda)$ by $f(c(\lambda,1),\dots,c(\lambda,r+s))$
-- statement:
--   Let $f\in S_{r,s}[x;y]$ be a supersymmetric polynomial. For every $\lambda\in\Lambda_{r,s}$, the element $f(L_1,\dots,L_{r+s})$ acts on the cell module $C_{r,s}(\lambda)$ as the scalar
--
--   $$
--   f\bigl(c(\lambda,1),\dots,c(\lambda,r),c(\lambda,r+1),\dots,c(\lambda,r+s)\bigr).
--   $$
--
--   Combined with the separation of content vectors (Lemma 2.12), this shows that supersymmetric polynomials in the Jucys–Murphy elements distinguish all cell modules, which is the key to the main theorem.
--
--   **Formalization Note** $f(L_1,\dots,L_{r+s})$ is `evalJM δ f`, $c(\lambda,\cdot)$ is `cVec δ λ`, and the cell module is the published `CellModule δ λ`; the statement is `evalJM δ f • v = f(c(λ,·)) • v` for every `v`. The platform's product is the opposite of the paper's; the up–down flip carries the paper's cell module to the published one, and central elements act by the same scalars.
-- source:
--   Jung–Kim, Supersymmetric polynomials and the center of the walled Brauer algebra, arXiv:1508.06469v2, p. 16, Corollary 3.3

import Mathlib
import Definitions.Def_WalledBrauer_Center_Setting

namespace WalledBrauer.Center
open WalledBrauer.Blocks MvPolynomial

theorem corollary_3_3 (r s : ℕ) (δ : ℂ) (f : MvPolynomial (Fin r ⊕ Fin s) ℂ)
    (hf : IsSupersymmetric f) (x : CellIndex r s) (v : CellModule δ x) :
    evalJM δ f • v = eval (cVec δ x) f • v := by sorry
end WalledBrauer.Center
