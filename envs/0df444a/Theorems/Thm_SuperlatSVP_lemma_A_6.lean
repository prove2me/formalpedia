-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_A_6
-- name    : SuperlatSVP.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:13.195281+00:00
-- url     : https://prove2.me/theorems/bb0c369b-e028-4d0d-8872-1478d4725752
-- title:
--   Lemma A.6 — Gaussian mass bound $Z_{\sqrt{e/n}}(L)\le C_n2^{\beta_Fn}$ for $\lambda_1(L)=1$
-- statement:
--   Let $\beta_F=\tfrac12\log_2(2e/\pi)$. There is a sequence $C_n\ge1$ with $\log_2C_n/n\to0$, independent of the lattice, such that every full-rank lattice $L\subset\mathbb R^n$ with $\lambda_1(L)=1$ satisfies
--   $$Z_{\sqrt{e/n}}(L)\le C_n\,2^{\beta_Fn},\qquad Z_\sigma(L)=\sum_{v\in L}e^{-\|v\|^2/(2\sigma^2)} .$$
--
--   Combined with Lemma A.7, this gives the point count at every radius (Theorem A.1).
--
--   Differences from the source:
--   - encoding: Gaussian masses as real sums → sums of nonnegative terms in [0,∞]; reason: Lean convention; the sums are finite for lattices, so no instance changes
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Appendix A.3, p.91 (PDF p.91), Lemma A.6, eq. (A.35)

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma A.6 (Gaussian mass bound). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Appendix A.3, p.91 (PDF p.91): "There is a sequence Cn ≥ 1
with log2 Cn = o(n), independent of the lattice, such that every lattice with λ1(L) = 1 satisfies
Z_{√(e/n)}(L) ≤ Cn 2^{βF n},   Zσ(L) = Σ_{v∈L} e^{−∥v∥²/(2σ²)}. (A.35)"
Here `β_F = 1/2 log2(2e/π)` (A.3).

**Formalization Note.** `log₂ C_n = o(n)` is `log₂ C_n / n → 0`. Lattices are full rank, `L = Bℤⁿ`;
`Z_σ` is `Zsig`, in `ℝ≥0∞`. -/
theorem lemma_A_6 :
    ∃ C : ℕ → ℝ, (∀ n, 1 ≤ C n) ∧
      Tendsto (fun n : ℕ => Real.logb 2 (C n) / n) atTop (nhds 0) ∧
      ∀ n : ℕ, ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → lam1 (lat B) = 1 →
        Zsig (Real.sqrt (Real.exp 1 / n)) (lat B) ≤
          ENNReal.ofReal (C n * (2 : ℝ) ^ ((1 / 2) * Real.logb 2 (2 * Real.exp 1 / Real.pi) * n)) := by sorry

end SuperlatSVP
