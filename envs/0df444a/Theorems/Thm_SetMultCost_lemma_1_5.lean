-- Prove2me | Theorems.Thm_SetMultCost_lemma_1_5
-- name    : SetMultCost.lemma_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:53:58.02468+00:00
-- url     : https://prove2.me/theorems/4e452f59-023d-46e5-99fa-a27f93e3fbab
-- title:
--   Lemma 1.5 — Binet–Minc identity
-- statement:
--   Let $d\le n$ and let $X$ be a $d\times n$ matrix with entries $x_{i,j}$. Then
--
--   $$\mathrm{RPerm}_{d,n}(X)=\sum_{\lambda\in\mathcal P(d)}(-1)^{d-|\lambda|}\prod_{S\in\lambda}(|S|-1)!\sum_{j=1}^n\prod_{i\in S}x_{i,j},\tag{1.6}$$
--
--   where $\mathcal P(d)$ is the set of partitions of $[d]$. The right side is a depth-four expression of the rectangular permanent, which is the source of the set-multilinearization gadget.
--
--   Differences from the source:
--   - generalization: a symbolic matrix → a matrix over any commutative ring; reason: the symbolic matrix over ℤ or over F is an instance
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Lemma 1.5, p.5

import Mathlib
import Definitions.Def_SetMultCost_RPerm

namespace SetMultCost

/-- **Lemma 1.5 (Binet–Minc Identity).** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.5: "Let d, n ∈ N with d ≤ n and let X be a d × n
symbolic matrix with X[i, j] = xi,j. Then, RPermd,n(X) = ∑_{λ∈P(d)} (−1)^{d−|λ|} ∏_{S∈λ} (|S| −
1)! ∑_{j=1}^n ∏_{i∈S} xi,j. (1.6)".

**Formalization Note.** Over any commutative ring and any matrix, which contains the symbolic matrix
over `ℤ` (the paper's remark after the lemma) and over any `F`. `λ` runs over the set partitions of
`Fin d`, as `Finpartition`. -/
theorem lemma_1_5 {R : Type*} [CommRing R] {d n : ℕ} (hdn : d ≤ n)
    (X : Matrix (Fin d) (Fin n) R) :
    RPerm X = ∑ lam : Finpartition (Finset.univ : Finset (Fin d)), binetMincTerm X lam := by sorry

end SetMultCost
