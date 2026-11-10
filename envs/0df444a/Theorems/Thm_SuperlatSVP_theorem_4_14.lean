-- Prove2me | Theorems.Thm_SuperlatSVP_theorem_4_14
-- name    : SuperlatSVP.theorem_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:22.026046+00:00
-- url     : https://prove2.me/theorems/332a10bf-3a30-48d1-bcc8-443407c326e3
-- title:
--   Theorem 4.14 (= Theorem 1.4, classical) — SVP in time $2^{(\beta-S-\frac12\log_2(1-2^{2S-2}))n+o(n)}$ and space $2^{Sn+o(n)}$ under (2.3)
-- statement:
--   Let $\tfrac12\log_2(4/3)\le\beta\le\tfrac12$ and $\tfrac12\log_2(4/3)\le S\le S_{\max}$, where $S_{\max}=(\beta+\tfrac12\log_2(4/3))/2$. Let $A_n>0$ with $\log_2A_n/n\to0$; the family is that of lattices satisfying the point-count bound (2.3), i.e. (1.5): $N_L(r\lambda_1(L))\le A_n2^{\beta n}r^n$ for $r\ge1$. Then there are:
--
--   - a randomized program $P$;
--   - a function $g$ with $g(n)/n\to0$;
--   - an exponent $K$;
--
--   such that for every $n\ge1$ and every invertible $B\in\mathbb Q^{n\times n}$ whose lattice satisfies (2.3), the program $P$ solves SVP on $B$ with probability at least $2/3$, within
--   $$\text{time }2^{(\beta-S-\frac12\log_2(1-2^{2S-2}))\,n+g(n)}\,(\ell+1)^K\quad\text{and space }2^{Sn+g(n)}\,(\ell+1)^K,$$
--   where $\ell$ is the input length.
--
--   This is the time–space tradeoff of the paper, with $S$ the space exponent. Corollary 1.5 is its instance at $\beta=\tfrac12\log_2(2e/\pi)$, $S=S_{\max}$.
--
--   **Formalization Note** $P$, $g$ and $K$ are chosen after $\beta$, $S$ and $A$ and before $n$ and $B$. Costs are bit time and bit space on every coin tape of the log-cost RAM `TwMSOCount.Main`.
--
--   Differences from the source:
--   - reading: "time" and "space" of an algorithm (no machine named) → bit time and bit space of the randomized log-cost rational RAM TwMSOCount.Main on every coin tape, times (ℓ+1)^K for the input length ℓ; reason: exact exponents need a random-access machine; "on every tape" is the stronger reading and the proof caps the work (p.44); the poly(ℓ) factor is the source's implicit dependence on the bit length (p.14)
--   - encoding: an input lattice given by a basis → an invertible rational basis B, input word n then B row by row, output the integer coefficient vector of a shortest nonzero vector; reason: algorithm inputs are finite words; real bases are not inputs
--   - encoding: a family of lattices satisfying (2.3) with A_n = 2^{o(n)} → every input basis whose lattice satisfies (2.3) for a fixed sequence A with A_n > 0 and log₂A_n/n → 0; reason: the family is the set of lattices obeying the bound; 2^{o(n)} as defined on p.87
--   - reading: the §4 analysis normalizes det L = 1 and is given an estimate λ with λ1(L) ≤ λ ≤ (1+n^{−2})λ1(L) (pp.32, 38) → neither is assumed: the input is any invertible rational basis and nothing else; reason: Theorem 4.14 is the classical clause of Theorem 1.4 (p.5), stated for input lattices without normalization or side input, and its proof runs "trials and length guesses sequentially" (p.44)
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.3, p.43 (PDF p.43), Theorem 4.14; Theorem 1.4, p.5, eqs. (1.5)–(1.6) (classical clause, α = S); Smax, p.38

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_SolvesSVPWithin

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Theorem 4.14 (SVP with spherical filters). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.3, p.43 (PDF p.43); the classical clause of
Theorem 1.4, p.5, with `α = S`: "For a family of n-dimensional lattices satisfying the point-count
bound (2.3) with 1/2 log2(4/3) ≤ β ≤ 1/2 and every 1/2 log2(4/3) ≤ S ≤ Smax, there exists a
randomized classical algorithm solving SVP with probability at least 2/3, in time
2^{(β−S−1/2 log2(1−2^{2S−2}))n+o(n)} and space 2^{Sn+o(n)}." Here `Smax = (β + 1/2 log2(4/3))/2` (p.38).

**Formalization Note.** The family is every input lattice satisfying (2.3) with a prefactor
sequence `A` (`A_n > 0`, `log₂ A_n / n → 0`), as in (1.5): `N_L(rλ₁) ≤ 2^{βn+o(n)}rⁿ`. One program
`P`, one `g` with `g(n)/n → 0` (time and space) and one exponent `K` are chosen after `β, S, A` and
before `n` and the basis. Inputs are invertible rational bases (input word: `n`, then `B` row by row);
the costs are bit time and bit space of the randomized log-cost RAM `TwMSOCount.Main` on every coin
tape, with the factor `(ℓ+1)^K` for the input length `ℓ`; success probability `≥ 2/3`
(`SolvesSVPWithin`). -/
theorem theorem_4_14 (β S : ℝ) (hβ₁ : (1 / 2) * Real.logb 2 (4 / 3) ≤ β) (hβ₂ : β ≤ 1 / 2)
    (hS₁ : (1 / 2) * Real.logb 2 (4 / 3) ≤ S) (hS₂ : S ≤ (β + (1 / 2) * Real.logb 2 (4 / 3)) / 2)
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n)
    (hAo : Tendsto (fun n : ℕ => Real.logb 2 (A n) / n) atTop (nhds 0)) :
    ∃ (P : TwMSOCount.Main.Program) (g : ℕ → ℝ) (K : ℕ),
      Tendsto (fun n : ℕ => g n / n) atTop (nhds 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
        PointCountBound (lat (B.map (fun q : ℚ => (q : ℝ)))) A β →
          SolvesSVPWithin P K
            ((2 : ℝ) ^ ((β - S - (1 / 2) * Real.logb 2 (1 - (2 : ℝ) ^ (2 * S - 2))) * n + g n))
            ((2 : ℝ) ^ (S * n + g n)) B := by sorry

end SuperlatSVP
