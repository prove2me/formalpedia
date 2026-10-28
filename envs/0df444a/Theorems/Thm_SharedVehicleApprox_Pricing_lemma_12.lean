-- Prove2me | Theorems.Thm_SharedVehicleApprox_Pricing_lemma_12
-- name    : SharedVehicleApprox.Pricing.lemma_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:32.018925+00:00
-- url     : https://prove2.me/theorems/51ce9938-0648-4ec2-9aaf-8480cd7fd555
-- title:
--   Lemma 12, p. 16 — Obj_m(q)/Obj_∞(q) = r_max(q)·G_{m−1}(q)/G_m(q) = A_m(q)
-- statement:
--   Let $n\ge1$, $m\ge1$, let $q$ be a state-independent quantile matrix, $I_{ij}$ per-ride rewards with reward curves $R_{ij}(q)=q\,I_{ij}(q)$, and $r\in\mathbb R^n$ traffic intensities with $r_j\ge0$ for all $j$ and $r_j>0$ for some $j$. Let $\pi$ be the product-form law (4), $\pi(x)=G_m^{-1}\prod_jr_j^{x_j}$ on $S_{n,m}$ with $G_m=\sum_{x\in S_{n,m}}\prod_jr_j^{x_j}$. Then the objective of $q$ in the $m$-unit system under $\pi$ satisfies
--   $$\mathrm{Obj}_m(q)=r_{\max}\frac{G_{m-1}}{G_m}\cdot\mathrm{Obj}_\infty(q),\qquad \max_iA_{i,m}=r_{\max}\frac{G_{m-1}}{G_m},$$
--   where $\mathrm{Obj}_\infty(q)=\sum_i(r_i/r_{\max})\sum_j\varphi_{ij}R_{ij}(q_{ij})$ and $A_{i,m}=\sum_{x\in S_{n,m}}\pi(x)\mathbf 1\{x_i>0\}$. In the paper's notation, $\mathrm{Obj}_m(q)/\mathrm{Obj}_\infty(q)=r_{\max}(q)G_{m-1}(q)/G_m(q)=A_m(q)$.
--
--   Together with Lemma 14 this bounds the loss from finitely many units by the factor $m/(m+n-1)$.
--
--   Differences from the source:
--   - encoding: Obj_m(q)/Obj_∞(q) = r_max(q)·G_{m−1}(q)/G_m(q) → Obj_m(q) = (r_max G_{m−1}/G_m)·Obj_∞(q); reason: the multiplicative form needs no Obj_∞(q) ≠ 0 (the paper's remark on p. 17); it is equivalent whenever Obj_∞(q) ≠ 0
--   - generalization: q a state-independent pricing policy, π its stationary law (4) with r = r(q) → any real matrix q and the product-form law (4) of any r ≥ 0 with a positive entry, not necessarily the traffic intensity of q; reason: by Theorem 2 the stationary law of q is (4) with r = r(q) ≥ 0, which has a positive entry; the identities hold for every such r
--   - encoding: A_m(q) := max_i A_{i,m}(q) → Finset.sup' over Fin n of the availabilities, n ≥ 1, m ≥ 1; reason: the maximum over a nonempty node set; G_{m−1} needs m ≥ 1
-- source:
--   Banerjee, Freund & Lykouris, Pricing and Optimization in Shared Vehicle Systems: An Approximation Framework, arXiv:1608.06819v4, p. 16 (PDF 17), Lemma 12; proof pp. 16–17 (PDF 17–18)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson
import Definitions.Def_SharedVehicleApprox_Pricing_Model

open Finset QueueingFundamentals.Networks Filter Topology

namespace SharedVehicleApprox.Pricing

/-- Lemma 12, p. 16: under the product-form law (4) with traffic intensities `r`, the objective
of the state-independent `q` in the `m`-unit system is `r_max · G_{m−1}/G_m` times its
infinite-unit objective, and `r_max · G_{m−1}/G_m` is the maximal availability `A_m(q)`. -/
theorem lemma_12 {n m : ℕ} [NeZero n] (hm : 1 ≤ m) (φ : Fin n → Fin n → ℝ)
    (I : Fin n → Fin n → ℝ → ℝ) (q : Fin n → Fin n → ℝ)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (hpos : ∃ j, 0 < r j) :
    obj n m φ I (toPolicy q) (productForm (fun j y => r j ^ y) m) =
        (rmax r * G r (m - 1) / G r m) * objInf φ I q r ∧
      univ.sup' univ_nonempty (fun i => availability m (productForm (fun j y => r j ^ y) m) i) =
        rmax r * G r (m - 1) / G r m := by sorry

end SharedVehicleApprox.Pricing
