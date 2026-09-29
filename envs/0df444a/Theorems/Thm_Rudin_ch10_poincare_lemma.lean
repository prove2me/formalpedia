-- Prove2me | Theorems.Thm_Rudin_ch10_poincare_lemma
-- name    : Rudin.ch10_poincare_lemma
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:26:44.234606+00:00
-- url     : https://prove2.me/theorems/7cd08794-8c10-497d-9abf-c7385d2ed650
-- title:
--   Theorem 10.39 — Poincaré's lemma
-- statement:
--   If $E \subseteq \mathbb{R}^n$ is convex and open and $\omega$ is a closed $k$-form of class $C'$ in $E$ with $k \ge 1$, then $\omega$ is exact: $\omega = d\eta$ for some $(k-1)$-form $\eta$ of class $C'$ in $E$. Closedness and exactness are stated through integrals over surfaces contained in $E$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 278, Definition 10.34 and Theorem 10.39

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.39 (Poincaré's lemma): on a convex open set every closed form of positive
order and class `C'` is exact.  Closedness and exactness are expressed through integrals over
surfaces lying in `E`, since a form is determined by those integrals. -/
theorem ch10_poincare_lemma (m n : ℕ) (E : Set (Fin n → ℝ)) (hE : IsOpen E) (hconv : Convex ℝ E)
    (ω : KForm (m + 1) n) (hω : ∀ i, ContDiffOn ℝ 1 (ω.coeff i) E)
    (hclosed : ∀ Φ : SimplexSurface (m + 1 + 1) n, ContDiff ℝ 1 Φ.map →
      (∀ u, Φ.map u ∈ E) → integralOverSimplex (extDeriv ω) Φ = 0) :
    ∃ η : KForm m n, (∀ i, ContDiffOn ℝ 1 (η.coeff i) E) ∧
      ∀ Φ : SimplexSurface (m + 1) n, ContDiff ℝ 1 Φ.map → (∀ u, Φ.map u ∈ E) →
        integralOverSimplex ω Φ = integralOverSimplex (extDeriv η) Φ := by sorry

end Rudin
