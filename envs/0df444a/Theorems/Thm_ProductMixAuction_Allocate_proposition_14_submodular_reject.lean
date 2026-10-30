-- Prove2me | Theorems.Thm_ProductMixAuction_Allocate_proposition_14_submodular_reject
-- name    : ProductMixAuction.Allocate.proposition_14_submodular_reject
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T15:21:51.469712+00:00
-- url     : https://prove2.me/theorems/d3205344-5866-4c72-933d-70985698a550
-- title:
--   Proposition 14 (reject-good direction), p. 21 — after shifting one bidder's bids by εe⁰, the SFM inputs h⁺ and h⁻ are submodular
-- statement:
--   Let $A=[p,(\mathcal B^j)_{j\in J},(m^j)_{j\in J},r]$ be an allocation problem in the sense of Definition 4 (p. 15) whose bids and prices are integral, fix a bidder $j\in J$ and a real number $\varepsilon$ with $|\varepsilon|<\tfrac14$. Let $\mathcal B'$ be the aggregate bid list obtained from $A$ by adding $\varepsilon e^{0}$ to every bid of bidder $j$, where $e^0$ is the unit vector of the reject good $0\in[n]_0$, and let
--   $$g(q)=f_{\mathcal B'}(q)+\sum_{i\in[n]} r_i\,q_i$$
--   be the Lyapunov function (5) of $\mathcal B'$ and the residual supply $r$. Then the two set functions on subsets $S\subseteq[n]$
--   $$h^+(S)=g\bigl(p+|\varepsilon|\,e^S\bigr)-g(p),\qquad h^-(S)=g\bigl(p-|\varepsilon|\,e^S\bigr)-g(p)$$
--   are submodular: $h(S\cup T)+h(S\cap T)\le h(S)+h(T)$ for all $S,T\subseteq[n]$.
--
--   This is the submodularity part of Proposition 14 (p. 21; proof pp. 36–37) for the shift direction of the reject good. ShiftProjectUnshift (Algorithm 5, p. 22) adds $\tfrac1{10}e^{i^*}$ to the bids of bidder $j^*$, where $i^*$ is a cycle-link good of the marginal bids graph; the vertices of that graph are all goods $[n]_0$, so $i^*=0$ can occur. Proposition 14 as printed fixes $i\in[n]$; this statement covers the remaining case $i=0$, and it is exactly what makes the two SFM calls of line 3 of Algorithm 5 legitimate when $i^*=0$.
--
--   **Formalization Note** Bids live on $[n]_0=$ `Fin (n + 1)`, prices on $[n]$ with $p_0=0$; the shift is `shiftList A.B j 0 ε` and $\mathcal B'$ is its `aggregate`. Integrality of bids and prices is assumed exactly as in the milestone `ProductMixAuction.Allocate.proposition_14`, whose submodularity conjuncts this statement mirrors with `i.succ` replaced by the reject good `0`.
-- source:
--   Baldwin, Goldberg, Klemperer, Lock, Solving Strong-Substitutes Product-Mix Auctions, arXiv:1909.07313v3, p. 21 Proposition 14 (submodularity of the Lyapunov-function SFM inputs, proof pp. 36-37), p. 22 Algorithm 5 line 3 (shift direction e^{i*} with i* a cycle-link good in [n]_0)

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

namespace ProductMixAuction.Allocate

theorem proposition_14_submodular_reject {n : ℕ} {J : Type*} [Fintype J] [DecidableEq J]
    (A : AllocProblem n J) (hA : IsAllocProblem A)
    (hbint : ∀ j, ∀ b ∈ A.B j, ∀ k, ∃ z : ℤ, b.v k = z)
    (hpint : ∀ i, ∃ z : ℤ, A.p i = z)
    (ε : ℝ) (hε : |ε| < 1 / 4) (j : J) :
    let B' := aggregate (shiftList A.B j 0 ε)
    NonmonotoneSubmod.Shared.Submodular (hPlus B' A.r A.p |ε|) ∧
      NonmonotoneSubmod.Shared.Submodular (hMinus B' A.r A.p |ε|) := by sorry

end ProductMixAuction.Allocate
