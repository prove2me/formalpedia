-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_2_12
-- name    : SinkhornHall.Supplement.lemma_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:07:02.102753+00:00
-- url     : https://prove2.me/theorems/fc69235e-49e8-5dfd-adf6-db5a80f57bac
-- title:
--   Lemma 2.12 — $D(N\|R(N))=D(N\mathbf 1\|r)$, and $D(N^*\|M^*)=D(p^*\|r)=\inf_{p\in\mathcal P}D(p\|r)$
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). For a matrix $N$, $R(N)_{ij}=(r_i/(N\mathbf 1)_i)N_{ij}$ and $C(N)_{ij}=(c_j/(N^\top\mathbf 1)_j)N_{ij}$ are its row and column normalizations, and the **Sinkhorn sequence** is
--
--   $$N_0=C(A),\qquad M_k=R(N_k),\qquad N_{k+1}=C(M_k)\quad(k=0,1,2,\dots).$$
--
--   $D(N\|M)=\sum_{i,j}N_{ij}\log(N_{ij}/M_{ij})$ is the KL divergence with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$; the sums of $N$ and $M$ may differ, so $D$ can be negative. The spaces are $\mathcal M=\{M: M_{ij}=0 \text{ if } A_{ij}=0,\ M_{ij}\ge0 \text{ if } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$ and $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$.
--
--   Let $(M^*,N^*)$ be the Sinkhorn limit, $p^*=N^*\mathbf 1$, and $\mathcal P=\{N\mathbf 1: N\in\mathcal C\}$ (2.9). Then
--
--   1. $D(N\|R(N))=D(N\mathbf 1\|r)$ for every $N\in\mathcal M$;
--   2. $$D(N^*\|M^*)=D(p^*\|r)=\inf_{p\in\mathcal P}D(p\|r).$$
--
--   Part (2) identifies the row marginal of the Sinkhorn limit as the KL projection of $r$ onto the polytope $\mathcal P$, which §3 computes explicitly.
--
--   Differences from the source:
--   - encoding: $D$ with values in $[-\infty,\infty]$ → `EReal` (`klDiv`, `matKL`), $\top$ when some $M_{ij}=0<N_{ij}$; reason: the paper's $\infty$ convention, same instances
--   - encoding: the Sinkhorn limit $(M^*,N^*)$ (the limit of $(M_k,N_k)$, Theorem 2.10) → a hypothesis that $(M_k,N_k)$ (or $N_k$) converges to the given matrices; reason: the paper defines the limit through Theorem 2.10, which the mission states separately; for the actual limit the statements coincide
--   - encoding: $R(N)$ for an $N\in\mathcal M$ with a zero row (undefined in the paper) → that row of `rowNormMat r N` is zero; reason: every term of both sides from such a row is $0$, so the identity is unaffected
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 2.12, p.9

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 2.12.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 2.12, p.9: "(1) D(N‖R(N)) = D(N1‖r) for N ∈ M.
(2) D(N*‖M*) = D(p*‖r) = inf_{p∈P} D(p‖r)", where (M*, N*) is the Sinkhorn limit (the limit of
(2.6), Theorem 2.10), "p* := N*1" and P is (2.9).

Setting of §2 (pp.4–5, p.8): `A` is a nonnegative `n × m` matrix with neither zero rows nor
zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not assumed.

**Formalization Note.** `D` is `matKL` / `klDiv` in `EReal`; the infimum is the `EReal`
infimum over `P = marginalPolytope A c`. The Sinkhorn limit enters as a hypothesis: part (2) holds
for every pair `(M*, N*)` that `(M_k, N_k)` converges to (Theorem 2.10 says it converges). For an
`N ∈ M` with a zero row the paper's `R(N)` is undefined; there `rowNormMat` puts a zero row, and
both sides of (1) get no contribution from that row. -/
theorem lemma_2_12 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    (∀ N ∈ supportSpace A, matKL N (rowNormMat r N) = SinkhornHall.klDiv (fun i => ∑ j, N i j) r) ∧
    (∀ Mstar Nstar : Matrix ι κ ℝ, Tendsto (sinkhornM A r c) atTop (𝓝 Mstar) →
      Tendsto (sinkhornN A r c) atTop (𝓝 Nstar) →
      matKL Nstar Mstar = SinkhornHall.klDiv (fun i => ∑ j, Nstar i j) r ∧
      SinkhornHall.klDiv (fun i => ∑ j, Nstar i j) r =
        ⨅ p ∈ marginalPolytope A c, SinkhornHall.klDiv p r) := by sorry

end SinkhornHall.Supplement
