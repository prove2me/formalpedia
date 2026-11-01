-- Prove2me | Theorems.Thm_QseriesFormalization_bilateralSum_congr
-- name    : QseriesFormalization.bilateralSum_congr
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:51:00.436661+00:00
-- url     : https://prove2.me/theorems/cf105d48-66d2-4ba1-a4d2-625d8b61b518
-- title:
--   Bilateral sums depend only on the values of $f$ on $[-n,n]$
-- statement:
--   Let $R$ be a commutative semiring and let $f,g:\mathbb{Z}\to R$. For every natural number $n$, if $f(j)=g(j)$ for all integers $j$ with $-n\le j\le n$, then the truncated bilateral sum of $f$ of order $n$ equals that of $g$:
--   $$\Big(\forall j,\ -n\le j\le n\Rightarrow f(j)=g(j)\Big)\ \Longrightarrow\ \mathrm{bilateralSum}\,f\,n=\mathrm{bilateralSum}\,g\,n .$$
--   Here $\mathrm{bilateralSum}\,f\,n$ is the symmetric finite truncation of a bilateral series $\sum_{j\in\mathbb{Z}}f(j)$, taken over $-n\le j\le n$.
--
--   This is a basic congruence lemma used when manipulating bilateral series (such as theta-type sums) in the book's later chapters.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Basic.lean#L211-L228

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib

/-!
# Basic objects for q-series formalization

Definitions used throughout *An Invitation to q-Series* (Hei-Chi Chan, 2011):
partitions, triangular and pentagonal numbers, the q-Pochhammer symbol,
finite sums, and Gaussian (q-binomial) coefficients.

These live in the root `QseriesFormalization` namespace so individual
chapters (in `QseriesFormalization.PartI.Ch02` etc.) can reuse them
without prefix juggling.
-/

open QseriesFormalization

/-! ### Partitions (Ch 1) -/

/-! ### Triangular and pentagonal numbers (Ch 1, Ch 4) -/

/-! ### q-Pochhammer (Ch 1) -/

variable {R : Type*} [CommRing R]

/-! ### Finite sums (Ch 3) -/

variable {R : Type*} [CommSemiring R]

theorem QseriesFormalization.bilateralSum_congr {f g : Int → R} :
    ∀ n : Nat, (∀ j : Int, -(n : Int) ≤ j ∧ j ≤ (n : Int) → f j = g j) →
      bilateralSum f n = bilateralSum g n := by sorry
