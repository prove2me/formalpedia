-- Prove2me | Theorems.Thm_SLQSolv_UnifConvex_lemma_2_3
-- name    : SLQSolv.UnifConvex.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:42.859974+00:00
-- url     : https://prove2.me/theorems/43294f17-97d6-4186-8576-1de4142a983f
-- title:
--   Lemma 2.3, p. 2279 — E∫|u − ΘX⁽ᵘ⁾|² ≥ γE∫|u|² for every Θ ∈ L²
-- statement:
--   Assume (H1)–(H2) and let $t\in[0,T)$. For $u\in\mathcal U[t,T]$ let $X^{(u)}$ solve
--
--   $$dX^{(u)}=[AX^{(u)}+Bu]ds+[CX^{(u)}+Du]dW,\quad s\in[t,T],\qquad X^{(u)}(t)=0.\qquad(2.6)$$
--
--   Then for every $\Theta\in L^2(t,T;\mathbb R^{m\times n})$ there is a constant $\gamma>0$ such that
--
--   $$\mathbb E\int_t^T|u(s)-\Theta(s)X^{(u)}(s)|^2ds\ \ge\ \gamma\,\mathbb E\int_t^T|u(s)|^2ds\qquad\forall u\in\mathcal U[t,T].\qquad(2.7)$$
--
--   In operator language, $u\mapsto u-\Theta X^{(u)}$ has a bounded inverse on $\mathcal U[t,T]$. It turns the completion of squares into uniform convexity in the proof of Theorem 4.5 and of Proposition 3.5.
--
--   **Formalization Note** $X^{(u)}$ is the state of Problem (SLQ)$^0$ from $(t,0)$; $\gamma$ may depend on $\Theta$, $t$ and the data. $|\cdot|$ is the Euclidean norm.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Lemma 2.3, pp. 2279–2280

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

/-- Lemma 2.3, pp. 2279–2280. With `X^{(u)}` the solution of (2.6) (the homogeneous state equation
from `(t, 0)`), for every `Θ ∈ L²(t, T; ℝ^{m×n})` there is `γ > 0` with (2.7)
`E∫ₜᵀ |u − ΘX^{(u)}|² ds ≥ γ E∫ₜᵀ |u|² ds` for all `u ∈ 𝒰[t, T]`. -/
theorem lemma_2_3 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω) (d : Data Ω n m)
    (h1 : H1 Bs d) (h2 : H2 Bs d)
    (t : ℝ≥0) (ht : t < d.T)
    (Θ : ℝ≥0 → Matrix (Fin m) (Fin n) ℝ) (hΘ : MatLpOn 2 t d.T Θ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ u, Adm Bs d t u →
      γ * sqNorm Bs d t u ≤
        sqNorm Bs d t (fun s ω => u s ω - Θ s *ᵥ state Bs d.hom t 0 u s ω) := by sorry

end SLQSolv.UnifConvex
