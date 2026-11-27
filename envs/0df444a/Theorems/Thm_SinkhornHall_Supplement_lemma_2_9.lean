-- Prove2me | Theorems.Thm_SinkhornHall_Supplement_lemma_2_9
-- name    : SinkhornHall.Supplement.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:06:14.910479+00:00
-- url     : https://prove2.me/theorems/487e9ad8-7192-5b3a-be6a-1f3c9b6d45a2
-- title:
--   Lemma 2.9 — $D(N_\ell\|M_\ell)$ is within $D(\tilde N^*\|(C/R)M_0)/\ell$ of the optimum of (2.7)
-- statement:
--   Throughout, $A$ is a nonnegative $n\times m$ real matrix with neither zero rows nor zero columns, $r\in\mathbb R^n$ and $c\in\mathbb R^m$ are positive vectors, $R=\sum_i r_i$ and $C=\sum_j c_j$ (it is **not** assumed that $R=C$). For a matrix $N$, $R(N)_{ij}=(r_i/(N\mathbf 1)_i)N_{ij}$ and $C(N)_{ij}=(c_j/(N^\top\mathbf 1)_j)N_{ij}$ are its row and column normalizations, and the **Sinkhorn sequence** is
--
--   $$N_0=C(A),\qquad M_k=R(N_k),\qquad N_{k+1}=C(M_k)\quad(k=0,1,2,\dots).$$
--
--   $D(N\|M)=\sum_{i,j}N_{ij}\log(N_{ij}/M_{ij})$ is the KL divergence with $0\log(0/x)=0$ and $x\log(x/0)=+\infty$ for $x>0$; the sums of $N$ and $M$ may differ, so $D$ can be negative. The spaces are $\mathcal M=\{M: M_{ij}=0 \text{ if } A_{ij}=0,\ M_{ij}\ge0 \text{ if } A_{ij}>0\}$, $\mathcal R=\{M\in\mathcal M: M\mathbf 1=r\}$ and $\mathcal C=\{M\in\mathcal M: M^\top\mathbf 1=c\}$.
--
--   Let $(\tilde M^*,\tilde N^*)$ be any minimizer of problem (2.7), $\inf\{D(N\|M): M\in\mathcal R,\ N\in\mathcal C\}$. Then for every positive integer $\ell$,
--
--   $$D(N_\ell\|M_\ell)-D(\tilde N^*\|\tilde M^*)\le\frac{D\big(\tilde N^*\,\big\|\,(C/R)M_0\big)}{\ell}.$$
--
--   This explicit $O(1/\ell)$ rate is the estimate that drives the analysis of the second algorithm (Theorem 4.3).
--
--   Differences from the source:
--   - encoding: $D$ with values in $[-\infty,\infty]$ → `EReal` (`klDiv`, `matKL`), $\top$ when some $M_{ij}=0<N_{ij}$; reason: the paper's $\infty$ convention, same instances
--   - encoding: the minimizer $(\tilde M^*,\tilde N^*)$ → any pair satisfying `IsMinimizer27` (minimal over all of $\mathcal R\times\mathcal C$); reason: the paper's "arbitrary minimizer"
--   - encoding: index sets $[n]$, $[m]$ → arbitrary finite types `ι`, `κ`; reason: every finite type is in bijection with some $[n]$; the empty types ($n=0$ or $m=0$, outside the paper's convention) only add trivially true or vacuous instances
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, Lemma 2.9, (2.8), p.9 (proof pp.8–9)

import Mathlib
import Definitions.Def_SinkhornHall_Model
import Definitions.Def_SinkhornHall_Analysis
import Definitions.Def_SinkhornHall_Supplement_KL

open Finset Filter Topology

namespace SinkhornHall.Supplement

/-- **Lemma 2.9 (rate of the objective).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, Lemma 2.9, (2.8), p.9: "For a positive integer ℓ > 0, it
holds D(N_ℓ‖M_ℓ) − D(Ñ*‖M̃*) ≤ D(Ñ*‖(C/R)M_0)/ℓ", where (p.8) "(M̃*, Ñ*)" is "an arbitrary
minimizer … of (2.7)".

Setting of §2 (pp.4–5, p.8): `A` is a nonnegative `n × m` matrix with neither zero rows nor
zero columns, `r`, `c` are positive vectors, `R := Σ r_i`, `C := Σ c_j`; `R = C` is not assumed.
`(M_k, N_k)` is the Sinkhorn sequence (2.6).

**Formalization Note.** `D` is `matKL` in `EReal`; the minimizer is any pair satisfying
`IsMinimizer27` (minimal over all of `R × C`). `(C/R)M_0` is the scalar multiple
`((Σ c)/(Σ r)) • M_0`, and the division by `ℓ` is `EReal` division by the positive integer `ℓ`. -/
theorem lemma_2_9 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, 0 < A i j) (hcol : ∀ j, ∃ i, 0 < A i j) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j)
    (Mt Nt : Matrix ι κ ℝ) (hmin : IsMinimizer27 A r c Mt Nt) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    matKL (sinkhornN A r c ℓ) (sinkhornM A r c ℓ) - matKL Nt Mt ≤
      matKL Nt (((∑ j, c j) / (∑ i, r i)) • sinkhornM A r c 0) / (ℓ : EReal) := by sorry

end SinkhornHall.Supplement
