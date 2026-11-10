-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_2_4
-- name    : SuperlatSVP.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:20.435201+00:00
-- url     : https://prove2.me/theorems/312e8116-6dd4-4db3-9f86-08c28e36bb4a
-- title:
--   Lemma 2.4 — Gaussian estimate $\rho_s(L)-1\le 3(n+1)A_n\big(b^2s^2n/(2\pi e\lambda_1(L)^2)\big)^{n/2}$
-- statement:
--   Let $L=B\mathbb Z^n$ be a full-rank lattice in dimension $n\ge1$. Let $\beta\ge0$, $b=2^\beta$, and suppose $L$ satisfies the point-count bound (2.3), $N_L(r\lambda_1(L))\le A_n b^n r^n$ for all $r\ge1$. Then for every $s>0$,
--   $$\rho_s(L)-1\le3(n+1)\,A_n\left(\frac{b^2s^2n}{2\pi e\,\lambda_1(L)^2}\right)^{n/2}.$$
--
--   This converts a point count into a bound on the Gaussian mass of the lattice. Through the Poisson summation formula it bounds the dual Gaussian mass that sizes the first superlattice (Lemma 4.1).
--
--   Differences from the source:
--   - encoding: ρ_s(L) − 1 as a real number → ρ_s(L ∖ {0}) in [0,∞]; reason: ρ_s(0) = 1 and the sum is finite, so no instance changes
--   - generalization: (2.3) with A_n = 2^{o(n)} independent of the lattice → the bound (2.3) for this one lattice with an arbitrary prefactor value A_n; reason: the lemma concerns one lattice and uses only the value A_n; the source's case is an instance
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.2, p.16 (PDF p.16), Lemma 2.4, eq. (2.10)

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 2.4 (Gaussian estimate). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §2.2, p.16 (PDF p.16): "For an n-dimensional
full-rank lattice L with (2.3), and s > 0, ρs(L) − 1 ≤ 3(n + 1)An (b²s²n/(2πeλ1(L)²))^{n/2}. (2.10)"

**Formalization Note.** `ρ_s(L) − 1` is written `ρ_s(L ∖ {0})` (`ρ_s(0) = 1`), in `ℝ≥0∞`. (2.3) is
`PointCountBound (lat B) A β` with `b = 2^β`, `β ≥ 0`, for an arbitrary prefactor sequence `A`. -/
theorem lemma_2_4 (n : ℕ) (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0)
    (A : ℕ → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hL : PointCountBound (lat B) A β) (s : ℝ) (hs : 0 < s) :
    rhoSet s ((lat B : Set (E n)) \ {0}) ≤
      ENNReal.ofReal (3 * ((n : ℝ) + 1) * A n *
        (((2 : ℝ) ^ β) ^ 2 * s ^ 2 * n / (2 * Real.pi * Real.exp 1 * lam1 (lat B) ^ 2)) ^
          ((n : ℝ) / 2)) := by sorry

end SuperlatSVP
