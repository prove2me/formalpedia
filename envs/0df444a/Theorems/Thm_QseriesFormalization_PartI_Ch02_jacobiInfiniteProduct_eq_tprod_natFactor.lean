-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch02_jacobiInfiniteProduct_eq_tprod_natFactor
-- name    : QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct_eq_tprod_natFactor
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:19:20.825609+00:00
-- url     : https://prove2.me/theorems/b3f242a7-520e-499b-9e54-0c843a6a50c8
-- title:
--   Reindexing the Jacobi product from $n\ge1$ to $n\ge0$
-- statement:
--   For all complex $q,z$, the infinite product $\prod_{n\ge1}(1-q^{2n})(1+zq^{2n-1})(1+z^{-1}q^{2n-1})$ (indexed by positive integers $n$, as a Lean `tprod`) equals the same product indexed by $n\in\mathbb{N}$ starting at $0$:
--   $$\prod_{n\ge1}(1-q^{2n})(1+zq^{2n-1})(1+z^{-1}q^{2n-1})=\prod_{n\ge0}(1-q^{2(n+1)})(1+zq^{2(n+1)-1})(1+z^{-1}q^{2(n+1)-1}).$$
--   There is no convergence hypothesis; it is a pure reindexing of the Lean infinite product. This is a technical step in Chapter 2's treatment of the Jacobi triple product.
--
--   Every reciprocal uses $0^{-1}=0$. A Lean tprod takes value $1$ if its family is not multipliable; this reindexing lemma does not assert convergence.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 2. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter02.lean#L161-L167

import Definitions.Def_QseriesFormalization_DefCoreQSeries
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

open QseriesFormalization
open QseriesFormalization.PartI
open QseriesFormalization.PartI.Ch02

variable {R : Type*} [Field R]

open Filter
open scoped Topology

theorem QseriesFormalization.PartI.Ch02.jacobiInfiniteProduct_eq_tprod_natFactor (q z : ℂ) :
    jacobiInfiniteProduct q z = ∏' n : ℕ, jacobiProductNatFactor q z n := by sorry
