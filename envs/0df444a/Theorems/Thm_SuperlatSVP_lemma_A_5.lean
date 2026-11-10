-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_A_5
-- name    : SuperlatSVP.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:19.517174+00:00
-- url     : https://prove2.me/theorems/38af9062-a610-4e5f-998b-f5b107498a45
-- title:
--   Lemma A.5 — compact centered count $C_L(T)\le B_{n,M}2^{\beta_Fn}T^{n/2}$ for $1\le T\le M$
-- statement:
--   Let $\beta_F=\tfrac12\log_2(2e/\pi)$. For every fixed $M>1$ there is a sequence $B_{n,M}\ge1$ with $\log_2B_{n,M}/n\to0$ such that every full-rank lattice $L\subset\mathbb R^n$ with $\lambda_1(L)=1$ satisfies
--   $$C_L(T)\le B_{n,M}\,2^{\beta_Fn}\,T^{n/2}\qquad(1\le T\le M),$$
--   where $C_L(T)=N_L(\sqrt T)$ counts the nonzero lattice vectors of squared length at most $T$. The factor does not depend on the lattice or on $T$.
--
--   This is the point count on a bounded range of radii obtained from the Fourier construction. Lemma A.6 turns it into a Gaussian mass bound.
--
--   Differences from the source:
--   - encoding: a count compared with a real bound → the count as an extended natural number, compared in [0,∞]; reason: Lean convention; no instance changes
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Appendix A.2, p.90 (PDF p.90), Lemma A.5, eq. (A.31); (A.2)–(A.3), p.87

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma A.5 (Compact centered count). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Appendix A.2, p.90 (PDF p.90): "For every fixed M > 1,
there is a sequence Bn,M ≥ 1 with log2 Bn,M = o(n) such that every lattice with λ1(L) = 1 satisfies
CL(T) ≤ Bn,M 2^{βF n} T^{n/2}   (1 ≤ T ≤ M). (A.31)
The factor is independent of the lattice and of T." Here `β_F = 1/2 log2(2e/π)` (A.3) and
`C_L(T) = N_L(√T)` (A.2).

**Formalization Note.** `log₂ B_{n,M} = o(n)` is `log₂ B_{n,M} / n → 0`. Lattices are full rank
(p.87), `L = Bℤⁿ`; counts in `ℝ≥0∞`. -/
theorem lemma_A_5 (M : ℝ) (hM : 1 < M) :
    ∃ Bs : ℕ → ℝ, (∀ n, 1 ≤ Bs n) ∧
      Tendsto (fun n : ℕ => Real.logb 2 (Bs n) / n) atTop (nhds 0) ∧
      ∀ n : ℕ, ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → lam1 (lat B) = 1 →
        ∀ T : ℝ, 1 ≤ T → T ≤ M →
          (pointCount (lat B) (Real.sqrt T) : ℝ≥0∞) ≤
            ENNReal.ofReal (Bs n * (2 : ℝ) ^ ((1 / 2) * Real.logb 2 (2 * Real.exp 1 / Real.pi) * n) *
              T ^ ((n : ℝ) / 2)) := by sorry

end SuperlatSVP
