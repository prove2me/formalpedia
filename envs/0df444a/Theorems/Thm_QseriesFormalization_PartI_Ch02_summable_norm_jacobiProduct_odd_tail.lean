-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch02_summable_norm_jacobiProduct_odd_tail
-- name    : QseriesFormalization.PartI.Ch02.summable_norm_jacobiProduct_odd_tail
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:20:42.854276+00:00
-- url     : https://prove2.me/theorems/afed8478-bb29-4ad5-ac54-f63037561365
-- title:
--   Absolute summability of the odd factors' tail in the Jacobi product
-- statement:
--   For complex numbers $q,c$ with $|q|<1$, the series of absolute values $\sum_{k\ge0}\big|c\,q^{2(k+1)-1}\big|=\sum_{k\ge0}|c|\,|q|^{2k+1}$ converges, i.e. the family $k\mapsto c\,q^{2k+1}$ is absolutely summable. (Here $2(k+1)-1=2k+1$.) This is the convergence estimate needed to show that the infinite product $\prod_k(1+c\,q^{2k+1})$, one of the odd factors in the Jacobi triple product, converges. It is a Chapter 2 preliminary.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 2. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter02.lean#L310-L325

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib

/-!
# Chapter 2 — Part I: First proof of Jacobi's triple product (functional equation)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 2, pp. 5–10.)

Chapter 2 proves Jacobi's triple product identity by exhibiting a function
that satisfies a functional equation `F(qz) = (1 + z) F(z)` and pinning it
down via growth/uniqueness arguments.

Truncated forms of the product and bilateral series are defined here as
recursive `def`s; the infinite forms `jacobiInfiniteProduct` and
`jacobiInfiniteSeries` use Mathlib's `tprod` and `tsum`. The final identity
`jacobiTripleProduct` is proved in `Chapter03.lean`, where the finite-JTP
machinery needed for the Gaussian-tail argument is available.
-/

variable {R : Type*} [Field R]

open Filter
open scoped Topology

theorem QseriesFormalization.PartI.Ch02.summable_norm_jacobiProduct_odd_tail (q c : ℂ) (hq : ‖q‖ < 1) :
    Summable fun k : ℕ => ‖c * q ^ (2 * (k + 1) - 1)‖ := by sorry
