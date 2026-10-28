-- Prove2me | Theorems.Thm_SU2Eposic_Extreme_lemma_2_9
-- name    : SU2Eposic.Extreme.lemma_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:47.962889+00:00
-- url     : https://prove2.me/theorems/c1fbb3b8-c1f4-40fa-ad07-e77f219d1fad
-- title:
--   Lemma 2.9 — the adjoint of α_{m,n,h} and the resolution of the identity Σ_h α α* = I
-- statement:
--   Let $m,n\in\mathbb N$.
--
--   1. For every $0\le h\le\min\{m,n\}$ the adjoint of $\alpha_{m,n,h}:P_{m+n-2h}\to P_m\otimes P_n$ (for the inner products (2.2)) is the map $\alpha^*_{m,n,h}:P_m\otimes P_n\to P_{m+n-2h}$ given by
--   $$\alpha^*_{m,n,h}(f(x,y))=\sqrt{c_{m,n,h}}\;\Delta_{xy}^{n-h}\Omega_{xy}^h\big(f(x,y)\big).$$
--   2. The maps $\alpha_{m,n,h}\alpha^*_{m,n,h}$ resolve the identity:
--   $$\sum_{h=0}^{\min\{m,n\}}\alpha_{m,n,h}\alpha^*_{m,n,h}=I_{P_m\otimes P_n}.$$
--
--   The lemma rewrites Theorem 2.7 in operator form; it is the step from which the isometry property of $\alpha_{m,n,h}$ (Proposition 2.10) is derived.
--
--   **Formalization Note** In the orthonormal canonical bases the adjoint is the conjugate transpose, so (1) says that the column of $\alpha_{m,n,h}^{\mathsf H}$ at $(l,j)$ is the coordinate vector of $\sqrt{c_{m,n,h}}\,\Delta_{xy}^{n-h}\Omega_{xy}^h(f^m_l\otimes f^n_j)$ in $P_{m+n-2h}$.
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 12, Lemma 2.9

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

namespace SU2Eposic.Extreme

open scoped Matrix

/-- **Lemma 2.9, p. 12.** For `m, n ∈ ℕ`:
(1) for `0 ≤ h ≤ min{m, n}`, the adjoint (conjugate transpose in the orthonormal canonical bases)
of `α_{m,n,h}` is `α*_{m,n,h}(f) = √c_{m,n,h} ∆^{n−h}_xy Ω^h_xy f`, i.e. its column at
`(l, j)` holds the coordinates in `P_{m+n−2h}` of `√c_{m,n,h} ∆^{n−h}_xy Ω^h_xy (f^m_l ⊗ f^n_j)`;
(2) `Σ_{h=0}^{min{m,n}} α_{m,n,h} α*_{m,n,h} = I_{P_m ⊗ P_n}`. -/
theorem lemma_2_9 (m n : ℕ) :
    (∀ h : ℕ, h ≤ min m n →
      (alpha (m + n - 2 * h) m n h)ᴴ =
        Matrix.of fun i (lj : Fin (m + 1) × Fin (n + 1)) =>
          coordX (m + n - 2 * h)
            (((Real.sqrt (c m n h) : ℝ) : ℂ) •
              (deltaXY ^ (n - h)) ((omegaXY ^ h) (canonXY m n lj.1 lj.2))) i) ∧
    ∑ h ∈ Finset.range (min m n + 1),
      alpha (m + n - 2 * h) m n h * (alpha (m + n - 2 * h) m n h)ᴴ = 1 := by sorry

end SU2Eposic.Extreme
