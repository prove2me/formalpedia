-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch03_exists_gaussianWeightedTailSummand_pairMajorant_bound
-- name    : QseriesFormalization.PartI.Ch03.exists_gaussianWeightedTailSummand_pairMajorant_bound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:20:55.797609+00:00
-- url     : https://prove2.me/theorems/1bcf78bb-dd80-4c14-b715-754d6162925a
-- title:
--   Uniform domination of the Gaussian-weighted tail summands by the Jacobi series terms
-- statement:
--   Let $q,z\in\mathbb{C}$ with $|q|<1$ and $M\in\mathbb{N}$. There is a real constant $C\ge0$ such that, for all sufficiently large $N$ and every $k\in\mathbb{N}$,
--   $$\big\|\mathrm{gaussianWeightedTailSummand}(q,z,N,M,k)\big\|\le C\cdot\Big(\|z^{-(k+M+1)}q^{(k+M+1)^2}\|+\|z^{k+M+1}q^{(k+M+1)^2}\|\Big).$$
--   Here the tail summand is the $q$-Pochhammer-weighted symmetric pair term of index $M+k$ (zero once $M+k\ge N$), and the right-hand factor is the sum of norms of the pair of Jacobi series terms $z^{\pm n}q^{n^2}$. This is the dominated-convergence estimate in Chapter 3's passage from the finite to the infinite Jacobi triple product.
--
--   Integer powers and reciprocals use Lean’s totalized convention: $0^{-1}=0$, so $0$ raised to a negative integer is $0$. The usual reciprocal interpretation applies when the base is nonzero.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 3. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter03.lean#L765-L817

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Chapter 3 — Part I: Second proof (Gaussian polynomials and the q-binomial theorem)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 3, pp. 11–20.)

Gaussian (q-binomial) coefficients are defined in `Basic.lean`. This file
states and proves the finite q-binomial theorem
`∏_{k=0}^{n-1} (1 + x q^k) = ∑_{k=0}^n [n choose k]_q q^{k(k-1)/2} x^k`.

The main theorem is proved by induction from the defining q-Pascal recursion
for Gaussian binomial coefficients.
-/

open QseriesFormalization
open QseriesFormalization.PartI
open QseriesFormalization.PartI.Ch03

variable {R : Type*} [CommRing R]

variable {R : Type*} [CommSemiring R]

variable {R : Type*} [CommRing R]

open Filter
open scoped Topology

theorem QseriesFormalization.PartI.Ch03.exists_gaussianWeightedTailSummand_pairMajorant_bound (q z : ℂ)
    (hq : ‖q‖ < 1) (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N in atTop, ∀ k,
        ‖gaussianWeightedTailSummand q z N M k‖ ≤
          C * Ch02.jacobiSeriesSymmetricPairNormMajorant q z (k + M) := by sorry
