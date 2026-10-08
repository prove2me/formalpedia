-- Prove2me | Theorems.Thm_QuantumLinSys_Fourier_lemma_12
-- name    : QuantumLinSys.Fourier.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:05.879971+00:00
-- url     : https://prove2.me/theorems/6d311ec2-13a8-4542-b0aa-55fae2d522d8
-- title:
--   Lemma 12, p. 11 — truncated Fourier integral approximates 1/x
-- statement:
--   Let $\kappa\ge1$ and $0<\varepsilon<1/2$. With $D_\kappa=[-1,-1/\kappa]\cup[1/\kappa,1]$, there are cutoffs
--   $y_J=\Theta(\kappa\sqrt{\log(\kappa/\varepsilon)})$ and
--   $z_K=\Theta(\sqrt{\log(\kappa/\varepsilon)})$, with absolute constants in both two-sided bounds, such that the integral $g_{y_J,z_K}$ of (21) satisfies
--   $$
--   \sup_{x\in D_\kappa}\left|g_{y_J,z_K}(x)-\frac1x\right|\le\varepsilon.
--   $$
--
--   The lemma converts the infinite Fourier integral for $1/x$ into one with finite integration limits.
--
--   **Formalization Note** The constants in $\Theta$ are chosen before $\kappa$ and $\varepsilon$. The condition-number convention $\kappa\ge1$ and Corollary 10's range $0<\varepsilon<1/2$ make the domain and logarithmic scales nondegenerate. The displayed supremum is prose for the pointwise bound; Lean states the bound for each $x\in D_\kappa$.
-- source:
--   Childs, Kothari and Somma, Quantum algorithm for systems of linear equations with exponentially improved dependence on precision, arXiv:1511.02306v2, p. 11, Lemma 12

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting

namespace QuantumLinSys.Fourier

/-- Lemma 12, p. 11: a truncated Gaussian Fourier integral approximates 1/x. -/
theorem lemma_12 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ κ ε : ℝ,
      1 ≤ κ → 0 < ε → ε < 1 / 2 →
        ∃ yJ zK : ℝ,
          c * (κ * Real.sqrt (Real.log (κ / ε))) ≤ yJ ∧
          yJ ≤ C * (κ * Real.sqrt (Real.log (κ / ε))) ∧
          c * Real.sqrt (Real.log (κ / ε)) ≤ zK ∧
          zK ≤ C * Real.sqrt (Real.log (κ / ε)) ∧
          ∀ x ∈ QuantumLinSys.Chebyshev.Dκ κ, ‖gTrunc yJ zK x - ((1 / x : ℝ) : ℂ)‖ ≤ ε := by sorry

end QuantumLinSys.Fourier
