-- Prove2me | Theorems.Thm_TeschlQM_Herglotz_herglotz_representation
-- name    : TeschlQM.Herglotz.herglotz_representation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:36:55.578919+00:00
-- url     : https://prove2.me/theorems/1b262760-cc34-416e-b57a-3661ef49cfda
-- title:
--   Theorem 3.20 — Herglotz representation: a Herglotz function with |F(z)| ≤ M/Im z is the Borel transform of a measure of mass ≤ M
-- statement:
--   Let $F$ be a Herglotz function, i.e. holomorphic on $\mathbb{C}_+$ with $\operatorname{Im} F > 0$ there, and suppose that for some constant $M$
--   $$|F(z)| \le \frac{M}{\operatorname{Im}(z)}, \qquad z \in \mathbb{C}_+ .$$
--   Then there is a Borel measure $\mu$ on $\mathbb{R}$ with $\mu(\mathbb{R}) \le M$ such that $F$ is the Borel transform of $\mu$:
--   $$F(z) = \int_{\mathbb{R}} \frac{d\mu(\lambda)}{\lambda - z}, \qquad z \in \mathbb{C}_+ .$$
--   Together with Theorem 3.10 this identifies the Herglotz functions obeying the growth bound with the finite Borel measures on $\mathbb{R}$; it is the step that turns the resolvent forms $\langle\psi, R_A(z)\psi\rangle$ into spectral measures in the proof of the spectral theorem.
--
--   **Formalization Note.** $M$ is a real number and $\mu(\mathbb{R}) \le M$ is `μ Set.univ ≤ ENNReal.ofReal M`; since a Herglotz function is nonzero on $\mathbb{C}_+$ the hypothesis already forces $M > 0$. The identity is required for every $z \in \mathbb{C}_+$, with the transform as the Bochner integral of `((t : ℂ) - z)⁻¹`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 107, Theorem 3.20

import Mathlib
import Definitions.Def_TeschlQM_Herglotz_IsHerglotz
import Definitions.Def_TeschlQM_Herglotz_borelTransform

open MeasureTheory

namespace TeschlQM.Herglotz

/-- Teschl, p. 107, Theorem 3.20 (Herglotz representation). If `F` is a Herglotz function
satisfying (3.86) `|F(z)| ≤ M / Im(z)` for `z ∈ ℂ₊`, then there is a Borel measure `μ` on `ℝ`
with `μ(ℝ) ≤ M` such that `F` is the Borel transform of `μ` on `ℂ₊`:
`F(z) = ∫_ℝ 1/(λ − z) dμ(λ)`. -/
theorem herglotz_representation (F : ℂ → ℂ) (hF : IsHerglotz F) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ M / z.im) :
    ∃ μ : Measure ℝ, μ Set.univ ≤ ENNReal.ofReal M ∧
      ∀ z : ℂ, 0 < z.im → F z = borelTransform μ z := by sorry

end TeschlQM.Herglotz
