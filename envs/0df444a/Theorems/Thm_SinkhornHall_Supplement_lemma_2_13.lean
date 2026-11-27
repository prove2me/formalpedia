-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_2_13
-- name    : SinkhornHall.Supplement.lemma_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:07:32.569402+00:00
-- url     : https://prove2.me/theorems/48b58c5c-718b-438d-a8f1-425e093d6dce
-- title:
--   Lemma 2.13 — $\frac1{2C}\|p(\ell)-p^*\|_1^2\le D(p(\ell)\|p^*)\le D(N^*\|(C/R)M_0)/\ell$
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). For a matrix $N$, $R(N)_{ij}=(r_i/(N\mathbf 1)_i)N_{ij}$ and $C(N)_{ij}=(c_j/(N^\top\mathbf 1)_j)N_{ij}$ are its row and column normalizations, and the **Sinkhorn sequence** is
--
--   $$N_0=C(A),\qquad M_k=R(N_k),\qquad N_{k+1}=C(M_k)\quad(k=0,1,2,\dots).$$
--
--   $D(N\|M)=\sum_{i,j}N_{ij}\log(N_{ij}/M_{ij})$ is the KL divergence with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$; the sums of $N$ and $M$ may differ, so $D$ can be negative. The spaces are $\mathcal M=\{M: M_{ij}=0 \text{ if } A_{ij}=0,\ M_{ij}\ge0 \text{ if } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$ and $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$.
--
--   Let $N^*$ be the limit of $N_k$, $p(k)=N_k\mathbf 1$ the row sums of $N_k$, and $p^*=N^*\mathbf 1$. For every positive integer $\ell$,
--
--   $$\frac1{2C}\|p(\ell)-p^*\|_1^2\ \le\ D(p(\ell)\|p^*)\ \le\ \frac{D\big(N^*\,\big\|\,(C/R)M_0\big)}{\ell}.$$
--
--   This is the convergence rate of the row marginals used to prove Theorem 4.3.
--
--   Differences from the source:
--   - encoding: $D$ with values in $[-\infty,\infty]$ → `EReal` (`klDiv`, `matKL`), $\top$ when some $M_{ij}=0<N_{ij}$; reason: the paper's $\infty$ convention, same instances
--   - encoding: the Sinkhorn limit $(M^*,N^*)$ (the limit of $(M_k,N_k)$, Theorem 2.10) → a hypothesis that $(M_k,N_k)$ (or $N_k$) converges to the given matrices; reason: the paper defines the limit through Theorem 2.10, which the mission states separately; for the actual limit the statements coincide
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 2.13, p.10

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 2.13 (rate of the row marginals).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 2.13, p.10: "For a positive integer ℓ, it holds
(1/(2C)) ‖p(ℓ) − p*‖₁² ≤ D(p(ℓ)‖p*) ≤ D(N*‖(C/R)M_0)/ℓ", where (p.9) "p(k) := N_k1" and
"p* := N*1", `N*` the Sinkhorn limit.

Setting of §2 (pp.4–5, p.8): `A` is a nonnegative `n × m` matrix with neither zero rows nor
zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not assumed.

**Formalization Note.** `p(ℓ)` and `p*` are the row sums of `N_ℓ` and `N*` (p.9 calls them
"column-marginals"). The Sinkhorn limit enters as a hypothesis `N_k → N*` (Theorem 2.10 says the
sequence converges). The left side is a real number cast to `EReal`; `D` is `klDiv` / `matKL`;
the division by `ℓ` is `EReal` division. -/
theorem lemma_2_13 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j)
    (Nstar : Matrix ι κ ℝ) (hN : Tendsto (sinkhornN A r c) atTop (𝓝 Nstar)) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ((((∑ i, |(∑ j, sinkhornN A r c ℓ i j) - ∑ j, Nstar i j|) ^ 2 / (2 * ∑ j, c j) : ℝ) : EReal)
        ≤ SinkhornHall.klDiv (fun i => ∑ j, sinkhornN A r c ℓ i j) (fun i => ∑ j, Nstar i j)) ∧
      SinkhornHall.klDiv (fun i => ∑ j, sinkhornN A r c ℓ i j) (fun i => ∑ j, Nstar i j) ≤
        matKL Nstar (((∑ j, c j) / (∑ i, r i)) • sinkhornM A r c 0) / (ℓ : EReal) := by sorry

end SinkhornHall.Supplement
