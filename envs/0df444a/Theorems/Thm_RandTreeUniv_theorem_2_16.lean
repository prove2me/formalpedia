-- Prove2me | Theorems.Thm_RandTreeUniv_theorem_2_16
-- name    : RandTreeUniv.theorem_2_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:11:08.437009+00:00
-- url     : https://prove2.me/theorems/18e97bd5-99e4-4941-b3dd-4907f4a87e55
-- title:
--   Theorem 2.16 — explicit fractional expectation-threshold bound
-- statement:
--   Let $X$ be a finite set and $F\subseteq2^X$ a non-empty family with $\emptyset\notin F$ that admits a $q$-spread probability measure for some $q\in(0,1)$. Let $\ell=\ell(F)$ be the maximal size of a minimal element of $F$, and let $p\le1$ satisfy
--
--   $$
--   p>200\,q\ln\ell .
--   $$
--
--   Then, with probability at least $1-1/\ell$, the $p$-random subset $X_p$ belongs to $\langle F\rangle$, that is, contains some member of $F$.
--
--   It is the quantitative form of the fractional expectation-threshold theorem of Frankston, Kahn, Narayanan and Park, implied by Bell (2023, Theorem 3) with $\varepsilon=1/\ell$; it is the probabilistic engine of the proof of Theorem 3.3. Since $\emptyset\notin F$ and $F\ne\emptyset$, $\ell\ge1$; for $\ell=1$ the bound is trivial.
--
--   Differences from the source:
--   - encoding: X_p, a random subset retaining each element with probability p → explicit sum of p^|Y|(1−p)^|X∖Y| over the subsets Y, with the hypothesis p ≤ 1; reason: the law of X_p; p ≤ 1 is needed for X_p to be defined
--   - encoding: probability measure ν on (F, 2^F) → weight function ν, nonnegative on F, summing to 1 over F; reason: a measure on a finite set is its mass function
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Theorem 2.16, p.13 (PDF 14) (implied by Bell 2023, Theorem 3)

import Mathlib
import Definitions.Def_RandTreeUniv_IsSpreadMeasure
import Definitions.Def_RandTreeUniv_binomialSubsetProb

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- **Theorem 2.16** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.13 (PDF 14); implied by Bell 2023, Theorem 3). Denote by
`ℓ = ℓ(F)` the maximal size of a minimal element of a non-empty family `F ⊆ 2^X` with `∅ ∉ F`
which admits a `q`-spread measure, and set `p > 200 q ln ℓ`. Then, with probability at least
`1 − 1/ℓ`, `X_p ∈ ⟨F⟩`, i.e. the `p`-random subset `X_p` contains some member of `F`.

**Formalization Note** `X` is a finite type. `q ∈ (0, 1)` is part of `IsSpreadMeasure`
(Definition 2.15). `p ≤ 1` is assumed so that `X_p` is defined. `ℓ ≥ 1` because `F` is nonempty
and `∅ ∉ F`; at `ℓ = 1` the bound is `0`. `ln` is `Real.log`. -/
theorem theorem_2_16 {X : Type*} [Fintype X] (F : Finset (Finset X)) (hF : F.Nonempty)
    (hempty : ∅ ∉ F) (q : ℝ) (ν : Finset X → ℝ) (hν : IsSpreadMeasure F q ν) (p : ℝ)
    (hp : 200 * q * Real.log (maxMinimalSize F) < p) (hp1 : p ≤ 1) :
    1 - 1 / (maxMinimalSize F : ℝ) ≤ binomialSubsetProb p (fun Y => ∃ A ∈ F, A ⊆ Y) := by sorry

end RandTreeUniv
