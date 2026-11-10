-- Prove2me | Theorems.Thm_SuperlatSVP_theorem_A_1
-- name    : SuperlatSVP.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:14.924385+00:00
-- url     : https://prove2.me/theorems/16312d59-6f1e-4bef-8bcc-18d35d76f9ae
-- title:
--   Theorem A.1 (= Proposition 1.3) — $1+C_L(T)\le A_n(2eT/(\pi\lambda_1(L)^2))^{n/2}$ for all $T\ge\lambda_1(L)^2$
-- statement:
--   Let $\beta_F=\tfrac12\log_2(2e/\pi)=0.3955994557\ldots$. There is a sequence $A_n\ge1$ with $\log_2A_n/n\to0$, independent of the lattice and the radius, such that every full-rank lattice $L\subset\mathbb R^n$ satisfies:
--
--   1. (A.4) for all $T\ge\lambda_1(L)^2$,
--   $$1+C_L(T)\le A_n\left(\frac{2eT}{\pi\lambda_1(L)^2}\right)^{n/2};$$
--   2. in radius notation, $1+N_L(r\lambda_1(L))\le A_n\,2^{\beta_Fn}\,r^n$ for all $r\ge1$;
--   3. (A.5) for every fixed $\delta>0$ and all sufficiently large $n$, uniformly over all lattices and radii,
--   $$1+N_L(r\lambda_1(L))\le2^{(\beta_F+\delta)n}\,r^n\qquad(r\ge1).$$
--
--   Here $N_L(R)$ counts the nonzero lattice vectors of length at most $R$ and $C_L(T)=N_L(\sqrt T)$. This is the worst-case point-count bound (2.3) with $\beta=\beta_F$, valid for every lattice. Substituting it into Theorem 4.14 gives Corollary 1.5.
--
--   **Formalization Note** In (A.5) the threshold dimension depends only on $\delta$.
--
--   Differences from the source:
--   - encoding: counts compared with real bounds → counts as extended natural numbers, compared in [0,∞]; reason: Lean convention; no instance changes
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Appendix A, p.87 (PDF p.87), Theorem A.1, eqs. (A.3)–(A.5); Proposition 1.3, p.4, eq. (1.4)

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Theorem A.1 (Uniform centered lattice-point bound) = Proposition 1.3. Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Appendix A, p.87
(PDF p.87): "Put βF = 1/2 log2(2e/π) = 0.395599455708 . . . . (A.3) There is a sequence An ≥ 1 with
log2 An = o(n), independent of the lattice and the radius, such that every full-rank lattice
L ⊂ ℝⁿ satisfies 1 + CL(T) ≤ An (2eT/(πλ1(L)²))^{n/2}   (T ≥ λ1(L)²). (A.4) In radius notation,
the same inequality is 1 + NL(rλ1(L)) ≤ An 2^{βF n} rⁿ for r ≥ 1. Equivalently, for every fixed
δ > 0, all sufficiently large dimensions satisfy 1 + NL(rλ1(L)) ≤ 2^{(βF+δ)n} rⁿ   (r ≥ 1), (A.5)
uniformly over all input lattices and all radii."

The conclusion has three parts: (A.4), its radius form, and (A.5).

**Formalization Note.** `C_L(T) = N_L(√T)` (A.2); `log₂ A_n = o(n)` is `log₂ A_n / n → 0`.
"Sufficiently large dimensions" in (A.5) is a threshold `n₀` depending only on `δ`. Lattices are
`L = Bℤⁿ` with `det B ≠ 0`, every `n`. Counts in `ℝ≥0∞`. -/
theorem theorem_A_1 :
    ∃ A : ℕ → ℝ, (∀ n, 1 ≤ A n) ∧
      Tendsto (fun n : ℕ => Real.logb 2 (A n) / n) atTop (nhds 0) ∧
      (∀ n : ℕ, ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ T : ℝ, lam1 (lat B) ^ 2 ≤ T →
        1 + (pointCount (lat B) (Real.sqrt T) : ℝ≥0∞) ≤
          ENNReal.ofReal (A n * (2 * Real.exp 1 * T / (Real.pi * lam1 (lat B) ^ 2)) ^
            ((n : ℝ) / 2))) ∧
      (∀ n : ℕ, ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ r : ℝ, 1 ≤ r →
        1 + (pointCount (lat B) (r * lam1 (lat B)) : ℝ≥0∞) ≤
          ENNReal.ofReal (A n *
            (2 : ℝ) ^ ((1 / 2) * Real.logb 2 (2 * Real.exp 1 / Real.pi) * n) * r ^ n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℝ,
        B.det ≠ 0 → ∀ r : ℝ, 1 ≤ r →
          1 + (pointCount (lat B) (r * lam1 (lat B)) : ℝ≥0∞) ≤
            ENNReal.ofReal ((2 : ℝ) ^
              (((1 / 2) * Real.logb 2 (2 * Real.exp 1 / Real.pi) + δ) * n) * r ^ n)) := by sorry

end SuperlatSVP
