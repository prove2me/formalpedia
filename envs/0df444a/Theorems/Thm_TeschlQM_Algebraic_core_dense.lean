-- Prove2me | Theorems.Thm_TeschlQM_Algebraic_core_dense
-- name    : TeschlQM.Algebraic.core_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T02:17:01.306332+00:00
-- url     : https://prove2.me/theorems/1738c0bc-af2d-4cc6-8d48-86fdfc7b4117
-- title:
--   Lemma 8.3 — 𝔇 = span{x^α e^{−x²/2}} is dense in L²(ℝⁿ)
-- statement:
--   For every $n \in \mathbb N_0$ the subspace
--   $$\mathfrak D = \operatorname{span}\{x^\alpha e^{-|x|^2/2} \mid \alpha \in \mathbb N_0^n\} \subseteq L^2(\mathbb R^n)$$
--   is dense in $L^2(\mathbb R^n)$.
--
--   Density makes $\mathfrak D$ an admissible domain for unbounded operators such as the angular momenta and the harmonic oscillator; it is the first step towards the Hermite basis of Theorem 8.5.
--
--   **Formalization Note.** $L^2(\mathbb R^n)$ is `Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))`, and $\mathfrak D$ is `core n 1`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 176, Lemma 8.3

import Mathlib
import Definitions.Def_TeschlQM_Algebraic_gaussCore

namespace TeschlQM.Algebraic

open MeasureTheory

/-- Teschl, Lemma 8.3, p. 176: the subspace `𝔇 = span{x^α e^{−x²/2} | α ∈ ℕ₀ⁿ}` of (8.20) is dense
in `L²(ℝⁿ)`. -/
theorem core_dense (n : ℕ) :
    Dense ((core n 1 : Submodule ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))) :
      Set (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))) := by sorry

end TeschlQM.Algebraic
