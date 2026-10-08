-- Prove2me | Theorems.Thm_PrivLearn_Parity_theorem_2_3
-- name    : PrivLearn.Parity.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:26.485609+00:00
-- url     : https://prove2.me/theorems/dbe3ef54-7aa6-49eb-8d09-4e7d64a8e06a
-- title:
--   Theorem 2.3 — the Laplace mechanism $f(z) + \mathrm{Lap}(\Delta/\varepsilon)$ is ε-differentially private
-- statement:
--   Let $f : D^n \to \mathbb R$ and let $\Delta > 0$ bound its global sensitivity: $|f(z) - f(z')| \le \Delta$ for all neighboring databases $z, z'$. Let $\varepsilon > 0$. Then the algorithm that on input $z$ returns
--
--   $$
--   f(z) + \eta, \qquad \eta \sim \mathrm{Lap}(\Delta/\varepsilon),
--   $$
--
--   is $\varepsilon$-differentially private.
--
--   This is the Laplace mechanism of Dwork, McSherry, Nissim and Smith; in §4 it makes the training errors of the candidate hypotheses private (Lemma 4.5).
--
--   **Formalization Note** The paper states the result for $\Delta = GS_f = \max_{z,z'} |f(z) - f(z')|$. Here $\Delta$ is any positive upper bound on the sensitivity, which covers $GS_f$ whenever it is positive: the maximum need not exist for an infinite domain $D$, and $GS_f = 0$ would give the degenerate scale $\mathrm{Lap}(0)$, which is not a probability measure.
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 8, Theorem 2.3

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy

open MeasureTheory

namespace PrivLearn.Parity

/-- Theorem 2.3 (Dwork et al.), p. 8 — the Laplace mechanism. If `Δ > 0` bounds the global
sensitivity of `f : Dⁿ → ℝ` (`|f(z) − f(z′)| ≤ Δ` for all neighbors `z, z′`), then the algorithm
that on input `z` returns `f(z) + η` with `η ∼ Lap(Δ/ε)` is ε-differentially private. -/
theorem theorem_2_3 {D : Type*} {n : ℕ} (f : (Fin n → D) → ℝ) (Δ ε : ℝ) (hΔ : 0 < Δ)
    (hε : 0 < ε) (hf : ∀ z z' : Fin n → D, PrivLearn.Generic.Neighbors z z' → |f z - f z'| ≤ Δ) :
    PrivLearn.Generic.IsDP (fun z => (PrivLearn.Generic.laplace (Δ / ε)).map (fun η => f z + η)) ε := by sorry

end PrivLearn.Parity
