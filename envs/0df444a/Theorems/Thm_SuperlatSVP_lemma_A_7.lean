-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_A_7
-- name    : SuperlatSVP.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:25.905006+00:00
-- url     : https://prove2.me/theorems/a277e0d1-e918-458d-b065-ad04008105d8
-- title:
--   Lemma A.7 — Gaussian mass scaling $Z_{a\sigma}(L)\le a^nZ_\sigma(L)$
-- statement:
--   For every full-rank lattice $L\subset\mathbb R^n$, every $\sigma>0$ and every $a\ge1$,
--   $$Z_{a\sigma}(L)\le a^n\,Z_\sigma(L),\qquad Z_\sigma(L)=\sum_{v\in L}e^{-\|v\|^2/(2\sigma^2)} .$$
--
--   Widening the Gaussian by the factor $a$ increases its lattice sum by at most $a^n$. This extends the compact-radius count of Lemma A.5 to all radii in Theorem A.1.
--
--   Differences from the source:
--   - encoding: Gaussian masses as real sums → sums of nonnegative terms in [0,∞]; reason: Lean convention; the sums are finite for lattices, so no instance changes
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Appendix A.3, p.91 (PDF p.91), Lemma A.7, eq. (A.39)

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma A.7 (Gaussian mass scaling). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), Appendix A.3, p.91 (PDF p.91): "For every full-rank lattice
L ⊂ ℝⁿ, every σ > 0, and every a ≥ 1, Z_{aσ}(L) ≤ aⁿ Z_σ(L). (A.39)"

**Formalization Note.** `Z_σ(L) = Σ_{v∈L} e^{−‖v‖²/(2σ²)}` ((A.35)) is `Zsig`, in `ℝ≥0∞`; `L = Bℤⁿ`
with `det B ≠ 0`. -/
theorem lemma_A_7 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (σ : ℝ) (hσ : 0 < σ)
    (a : ℝ) (ha : 1 ≤ a) :
    Zsig (a * σ) (lat B) ≤ ENNReal.ofReal (a ^ n) * Zsig σ (lat B) := by sorry

end SuperlatSVP
