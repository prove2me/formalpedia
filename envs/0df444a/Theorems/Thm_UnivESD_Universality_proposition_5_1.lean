-- Prove2me | Theorems.Thm_UnivESD_Universality_proposition_5_1
-- name    : UnivESD.Universality.proposition_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:50.517306+00:00
-- url     : https://prove2.me/theorems/2f9f5948-ace2-4d56-bff9-8dda90eb5f12
-- title:
--   Proposition 5.1 (lower tail bound): $\mathbf P(\mathrm{dist}(X,W)\le c\sqrt{n-d})=O(\exp(-n^{0.01}))$
-- statement:
--   Let $x$ be a complex random variable with zero mean and unit variance, and let $X=v+(x_1,\dots,x_n)$ be a row of $A_n$: $x_1,\dots,x_n$ are i.i.d. copies of $x$ and $v\in\mathbb C^n$ is the corresponding deterministic row of $M_n$. Let $0<c<1$. Then there is a constant $C$, depending on $c$ (and the law of $x$), such that for every $n$, every $1\le d\le n-n^{0.99}$ and every deterministic $d$-dimensional subspace $W$ of $\mathbb C^n$,
--   $$\mathbf P\bigl(\mathrm{dist}(X,W)\le c\sqrt{n-d}\bigr)\le C\exp(-n^{0.01}).$$
--
--   A random vector with independent standardized entries is, with overwhelming probability, not much closer to a fixed subspace of large codimension than its expected distance $\sqrt{n-d}$. This handles the rows between $(1-\delta)n$ and $n-n^{0.99}$.
--
--   **Formalization Note.** The probability is computed under the product law $\nu^{\otimes n}$ of $(x_1,\dots,x_n)$. The statement quantifies over every deterministic shift $v$ (the paper's "a row of $A_n$" for arbitrary deterministic $M_n$; its proof removes $v$ by enlarging $W$); the constant $C$ is fixed after $c$ and before $n,d,W,v$. Distances are Euclidean in $\mathbb C^n$.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2047 (PDF 25), Proposition 5.1

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Proposition 5.1 (lower tail bound), p. 2047. `ν` is the law of `x`; a row of `A_n` is
`v + (x_1, …, x_n)` with `v` the (deterministic) row of `M_n` and `x_i` i.i.d. with law `ν`. -/
theorem proposition_5_1 (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν2 : MemLp id 2 ν)
    (hν0 : ∫ x, x ∂ν = 0) (hν1 : ∫ x, ‖x‖ ^ 2 ∂ν = 1) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ C : ℝ, ∀ n d : ℕ, 1 ≤ d → (d : ℝ) ≤ n - (n : ℝ) ^ (0.99 : ℝ) →
      ∀ W : Submodule ℂ (EuclideanSpace ℂ (Fin n)), Module.finrank ℂ W = d →
        ∀ v : EuclideanSpace ℂ (Fin n),
          (Measure.pi fun _ : Fin n => ν)
              {ξ | Metric.infDist (v + WithLp.toLp 2 ξ) (W : Set (EuclideanSpace ℂ (Fin n)))
                ≤ c * Real.sqrt (n - d)}
            ≤ ENNReal.ofReal (C * Real.exp (-(n : ℝ) ^ (0.01 : ℝ))) := by sorry

end UnivESD.Universality
