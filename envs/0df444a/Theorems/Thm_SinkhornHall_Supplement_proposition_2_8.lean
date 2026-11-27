-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_proposition_2_8
-- name    : SinkhornHall.Supplement.proposition_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:05:46.605806+00:00
-- url     : https://prove2.me/theorems/f8006b09-fbfa-533e-9725-c3fd24610f63
-- title:
--   Proposition 2.8 — three-, four- and five-point properties of the Sinkhorn sequence
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). For a matrix $N$, $R(N)_{ij}=(r_i/(N\mathbf 1)_i)N_{ij}$ and $C(N)_{ij}=(c_j/(N^\top\mathbf 1)_j)N_{ij}$ are its row and column normalizations, and the **Sinkhorn sequence** is
--
--   $$N_0=C(A),\qquad M_k=R(N_k),\qquad N_{k+1}=C(M_k)\quad(k=0,1,2,\dots).$$
--
--   $D(N\|M)=\sum_{i,j}N_{ij}\log(N_{ij}/M_{ij})$ is the KL divergence with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$; the sums of $N$ and $M$ may differ, so $D$ can be negative. The spaces are $\mathcal M=\{M: M_{ij}=0 \text{ if } A_{ij}=0,\ M_{ij}\ge0 \text{ if } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$ and $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$.
--
--   For every $M\in\mathcal R$ and $N\in\mathcal C$:
--
--   1. (3-point property) for every $k\ge1$, $$D(N\|N_k)+D(N_k\|M_{k-1})=D(N\|M_{k-1});$$
--   2. (4-point property) for every $k\ge0$, $$D(N\|M_k)\le D(N\|N_k)+D(N\|M);$$
--   3. (5-point property) for every $k\ge1$, $$D(N_k\|M_{k-1})+D(N\|M_k)\le D(N\|M)+D(N\|M_{k-1}).$$
--
--   These are the Csiszár–Tusnády properties of the alternating minimization; summed over $k$ they give the convergence rate of Lemma 2.9 and the convergence of Theorem 2.10.
--
--   Differences from the source:
--   - encoding: $D$ with values in $[-\infty,\infty]$ → `EReal` (`klDiv`, `matKL`), $\top$ when some $M_{ij}=0<N_{ij}$; reason: the paper's $\infty$ convention, same instances
--   - encoding: the 3- and 5-point properties for $k\ge1$ (they involve $M_{k-1}$) → stated with $k+1$ in place of $k$ for every $k\ge0$; reason: same instances
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Proposition 2.8, p.8 (proof in Appendix A, p.20)

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Proposition 2.8 (three-, four- and five-point properties).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Proposition 2.8, p.8 (proof in Appendix A, p.20):
"For M ∈ R, N ∈ C, the following hold:
(3-point property) D(N‖N_k) + D(N_k‖M_{k−1}) = D(N‖M_{k−1}).
(4-point property) D(N‖M_k) ≤ D(N‖N_k) + D(N‖M).
(5-point property) D(N_k‖M_{k−1}) + D(N‖M_k) ≤ D(N‖M) + D(N‖M_{k−1})."

Setting of §2 (pp.4–5, p.8): `A` is a nonnegative `n × m` matrix with neither zero rows nor
zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not assumed.
`(M_k, N_k)` is the Sinkhorn sequence (2.6): `N_0 = C(A)`, `M_k = R(N_k)`, `N_{k+1} = C(M_k)`.

**Formalization Note.** `D` is `matKL` (valued in `EReal`, `⊤` when some `M_ij = 0 < N_ij`).
The 3- and 5-point properties involve `M_{k−1}`, so they are stated for `k ≥ 1`, written with
`k + 1` in place of `k`; the 4-point property is stated for every `k ≥ 0`. -/
theorem proposition_2_8 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j)
    (M N : Matrix ι κ ℝ) (hM : M ∈ rowSpace A r) (hN : N ∈ colSpace A c) :
    (∀ k : ℕ, matKL N (sinkhornN A r c (k + 1)) +
        matKL (sinkhornN A r c (k + 1)) (sinkhornM A r c k) = matKL N (sinkhornM A r c k)) ∧
    (∀ k : ℕ, matKL N (sinkhornM A r c k) ≤ matKL N (sinkhornN A r c k) + matKL N M) ∧
    (∀ k : ℕ, matKL (sinkhornN A r c (k + 1)) (sinkhornM A r c k) +
        matKL N (sinkhornM A r c (k + 1)) ≤ matKL N M + matKL N (sinkhornM A r c k)) := by sorry

end SinkhornHall.Supplement
