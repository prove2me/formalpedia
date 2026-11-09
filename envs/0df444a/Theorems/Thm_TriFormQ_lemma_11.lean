-- Prove2me | Theorems.Thm_TriFormQ_lemma_11
-- name    : TriFormQ.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:24.855604+00:00
-- url     : https://prove2.me/theorems/a801063d-8941-4082-bbdf-d2bd39d0627d
-- title:
--   Lemma 11: $2\,\mathrm{rk}(B|_{\mathrm{coker}A\times\ker A})+\mathrm{rk}A\le\mathrm{rk}B+\mathrm{rk}(A+B)$
-- statement:
--   Let $K$ be an arbitrary field, $m,n$ positive integers and $A,B\in M_{m\times n}(K)$. Then
--
--   $$2\,\mathrm{rk}\big(B|_{\operatorname{coker}A\times\ker A}\big)+\mathrm{rk}(A)\ \le\ \mathrm{rk}(B)+\mathrm{rk}(A+B),$$
--
--   where $\ker A=\{x:Ax=0\}$, $\operatorname{coker}A=\{y:y^\top A=0\}$, and the left-hand rank is that of the bilinear form $(y,x)\mapsto y^\top Bx$ restricted to $\operatorname{coker}A\times\ker A$.
--
--   This rank inequality drives the pivot step: restricting a space of matrices to the kernel and cokernel of a high-rank member reduces its maximum rank by a constant factor.
--
--   Differences from the source:
--   - encoding: $\operatorname{coker}A$ and $\mathrm{rk}(B|_{\operatorname{coker}A\times\ker A})$ → the left kernel $\{y: y^\top A=0\}$ and the rank of the induced map $\ker A\to(\operatorname{coker}A)^*$; reason: the paper's usage (pivoting restricts to "the left- and right-kernel", p.32)
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 11, p.31 (PDF p.34)

import Definitions.Def_TriFormQ_restrictRank

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 11, p.31 (PDF p.34): "Let
F be an arbitrary field, and m, n positive integers. Let A, B ∈ M_{m×n}(F). Then
2 rk(B|_{coker A × ker A}) + rk(A) ≤ rk(B) + rk(A + B)."

**Formalization Note.** `coker A` is the left kernel `{y | yᵀA = 0}` and
`rk(B|_{coker A × ker A})` is the rank of the restricted bilinear form (`restrictRank B A`). The
field is arbitrary, not necessarily finite. -/
theorem lemma_11 {K : Type} [Field K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A B : Matrix (Fin m) (Fin n) K) :
    2 * restrictRank B A + A.rank ≤ B.rank + (A + B).rank := by sorry

end TriFormQ
