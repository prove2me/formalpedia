-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_2_7
-- name    : SinkhornHall.Supplement.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:05:18.266377+00:00
-- url     : https://prove2.me/theorems/e1207b20-9e44-4c81-a1b7-8bf5b4a438d3
-- title:
--   Lemma 2.7 — $\inf_{M\in\mathcal R}D(N\|M)=D(N\|R(N))$ and $\inf_{N\in\mathcal C}D(N\|M)=D(C(M)\|M)$
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). For a matrix $N$, $R(N)_{ij}=(r_i/(N\mathbf 1)_i)N_{ij}$ and $C(N)_{ij}=(c_j/(N^\top\mathbf 1)_j)N_{ij}$ are its row and column normalizations, and the **Sinkhorn sequence** is
--
--   $$N_0=C(A),\qquad M_k=R(N_k),\qquad N_{k+1}=C(M_k)\quad(k=0,1,2,\dots).$$
--
--   $D(N\|M)=\sum_{i,j}N_{ij}\log(N_{ij}/M_{ij})$ is the KL divergence with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$; the sums of $N$ and $M$ may differ, so $D$ can be negative. The spaces are $\mathcal M=\{M: M_{ij}=0 \text{ if } A_{ij}=0,\ M_{ij}\ge0 \text{ if } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$ and $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$.
--
--   Then
--
--   1. $\displaystyle\inf_{M\in\mathcal R}D(N\|M)=D(N\|R(N))$ for every $N\in\mathcal M$;
--   2. $\displaystyle\inf_{N\in\mathcal C}D(N\|M)=D(C(M)\|M)$ for every $M\in\mathcal M$ (with no zero column, so that $C(M)$ is defined).
--
--   So $M_k=R(N_k)$ and $N_{k+1}=C(M_k)$ are the two half-steps of alternating minimization of (2.7).
--
--   Differences from the source:
--   - encoding: $D$ with values in $[-\infty,\infty]$ → `EReal` (`matKL`), $\top$ when some $M_{ij}=0<N_{ij}$, infima in `EReal`; reason: the paper's $\infty$ convention, same instances
--   - encoding: part (2) for $M\in\mathcal M$ → for $M\in\mathcal M$ with every column nonzero; reason: $C(M)_{ij}=(c_j/q_j)M_{ij}$ (p.6) is undefined when $q_j=(M^\top\mathbf 1)_j=0$; the condition only excludes the matrices where the right side is undefined
--   - encoding: $R(N)$ for an $N\in\mathcal M$ with a zero row (undefined in the paper) → that row of `rowNormMat r N` is zero; reason: that row contributes $0$ to both sides, so part (1) holds there as well
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 2.7, p.8 (proof in Appendix A, pp.19–20)

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL

open Finset

namespace SinkhornHall.Supplement

/-- **Lemma 2.7 (the Sinkhorn steps are the alternating minimizations of (2.7)).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 2.7, p.8 (proof in Appendix A, pp.19–20):
"(1) inf_{M∈R} D(N‖M) = D(N‖R(N)) (N ∈ M).
(2) inf_{N∈C} D(N‖M) = D(C(M)‖M) (M ∈ M)."

Setting of §2 (pp.4–5, p.8): `A` is a nonnegative `n × m` matrix with neither zero rows nor
zero columns, `r`, `c` are positive vectors; `R = C` is not assumed.

**Formalization Note.** `D` is `matKL` (valued in `EReal`, `⊤` when some `M_ij = 0 < N_ij`) and the
infima are `EReal` infima over `R = rowSpace A r` and `C = colSpace A c`. The paper's `C(M)` is
defined only when every column of `M` is nonzero (p.6, division by `q_j = (M⊤1)_j`); part (2) is
stated for those `M ∈ M`. (For an `M` with a zero column every `N ∈ C` has `D(N‖M) = ∞`.) Part (1)
is stated for every `N ∈ M`: on a zero row of `N`, `rowNormMat` puts a zero row, and that row
contributes `0` to both sides. -/
theorem lemma_2_7 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) :
    (∀ N ∈ supportSpace A,
      ⨅ M ∈ rowSpace A r, matKL N M = matKL N (rowNormMat r N)) ∧
    (∀ M ∈ supportSpace A, (∀ j, ∃ i, M i j ≠ 0) →
      ⨅ N ∈ colSpace A c, matKL N M = matKL (colNormMat c M) M) := by sorry

end SinkhornHall.Supplement
