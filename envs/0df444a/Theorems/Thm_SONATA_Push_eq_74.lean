-- Prove2me | Theorems.Thm_SONATA_Push_eq_74
-- name    : SONATA.Push.eq_74
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:14:33.187003+00:00
-- url     : https://prove2.me/theorems/c47c3bf0-a461-41a0-838d-9f11cb239428
-- title:
--   (74), p. 28 — the φ-weighted average of the trackers follows the average gradient
-- statement:
--   Consider Problem (P) under Assumption A and SONATA (Algorithm 3) under Assumptions B′, C and E, with the constants (15) and a solution $x^\star$. Let $\alpha\in(0,1]$ and let $(x^\nu,y^\nu,\hat x^\nu,\phi^\nu)$ be a run of Algorithm 3. Then for every $\nu=0,1,\dots$
--   $$\frac1m\sum_{i=1}^m\phi_i^{\nu+1}y_i^{\nu+1}=\frac1m\sum_{i=1}^m\phi_i^\nu y_i^\nu+\overline{\nabla f}^{\nu+1}-\overline{\nabla f}^\nu,$$
--   and consequently, by the initialization $\phi_i^0=1$, $y_i^0=\nabla f_i(x_i^0)$,
--   $$\bar y_\phi^\nu=\overline{\nabla f}^\nu\qquad\text{for all }\nu.$$
--
--   This is the push-sum replacement of the tracking identity of the undirected case: the gradient average is carried by the $\phi$-weighted average of the $y_i$.
--
--   **Formalization Note** The second identity is the consequence the paper uses in Lemma I.3 and Proposition 4.3; it is stated with (74) in one item.
-- source:
--   Sun, Daneshmand & Scutari, Distributed Optimization Based on Gradient-tracking Revisited, arXiv:1905.02637v2, p. 28, (74), with Algorithm 3's Data

import Mathlib
import Definitions.Def_SONATA_Push_Network

namespace SONATA.Push

/-- (74) (p. 28): the `φ`-weighted average of the trackers follows the average gradient,
`(1/m) Σ_i φ_i^{ν+1} y_i^{ν+1} = (1/m) Σ_i φ_i^ν y_i^ν + ∇f̄^{ν+1} − ∇f̄^ν`; with Algorithm 3's Data
(`φ^0 = 1`, `y_i^0 = ∇f_i(x_i^0)`) this gives `ȳ_φ^ν = ∇f̄^ν` for every `ν`. -/
theorem eq_74
    {m d : ℕ} (K O : Set (SONATA.Undir.E d)) (f : Fin m → SONATA.Undir.E d → ℝ) (G : SONATA.Undir.E d → ℝ) (μ L : ℝ)
    (ft : Fin m → SONATA.Undir.E d → SONATA.Undir.E d → ℝ) (μt Lt Dl Du : Fin m → ℝ) (xstar : SONATA.Undir.E d)
    (Edges : ℕ → Fin m → Fin m → Prop) (B : ℕ) (C : ℕ → Matrix (Fin m) (Fin m) ℝ) (cl : ℝ)
    (hP : ProblemHyp K O f G μ L ft μt Lt Dl Du xstar) (hN : NetworkHyp Edges B C cl)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x y xh : ℕ → Fin m → SONATA.Undir.E d) (φ : ℕ → Fin m → ℝ) (hrun : IsRun K f G ft C α x y xh φ) :
    (∀ ν : ℕ, wavg (φ (ν + 1)) (y (ν + 1)) =
        wavg (φ ν) (y ν) + gradAvg f (x (ν + 1)) - gradAvg f (x ν)) ∧
      ∀ ν : ℕ, wavg (φ ν) (y ν) = gradAvg f (x ν) := by sorry

end SONATA.Push
