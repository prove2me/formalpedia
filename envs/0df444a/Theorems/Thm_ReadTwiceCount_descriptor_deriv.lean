-- Prove2me | Theorems.Thm_ReadTwiceCount_descriptor_deriv
-- name    : ReadTwiceCount.descriptor_deriv
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:42.015058+00:00
-- url     : https://prove2.me/theorems/2530d749-76fd-4ee8-b367-d2a44b5d3ba5
-- title:
--   §4 (8) — the partial derivatives of the descriptor
-- statement:
--   Let $\mathcal F$ be a nonsingular descriptor and let $y$ be inputs with every $y_j\ge1$. Then $\mathcal F$ is differentiable in each input, with
--   $$\frac{\partial\mathcal F}{\partial y_i}=\frac{\mathcal F(\mathcal F-1)}{y_i(y_i+1)}\quad(i\in I_-),\qquad \frac{\partial\mathcal F}{\partial y_i}=-\frac{\mathcal F(\mathcal F-1)}{y_i+1}\quad(i\in I_+).$$
--
--   Thus $\mathrm{NEQ}$ edges carry positive dependence and $\mathrm{EQ}$ edges negative dependence. These derivatives are the local weights of the sensitivity budget.
--
--   Differences from the source: none.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), §4, display (8), p.5

import Mathlib
import Definitions.Def_ReadTwiceCount_Descriptor

namespace ReadTwiceCount

/-- **The derivatives of a descriptor (8)** (He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), §4, display (8),
p.5): for finite inputs `yᵢ ≥ 1`,
`∂ℱ/∂yᵢ = ℱ(ℱ − 1)/(yᵢ(yᵢ + 1))` for `i ∈ I−` (NEQ) and `∂ℱ/∂yᵢ = −ℱ(ℱ − 1)/(yᵢ + 1)` for `i ∈ I+`
(EQ).

**Formalization Note** Stated for every nonsingular descriptor (not `t = 0` with no inputs, the case
the paper excludes, p.4) as a `HasDerivAt` of ℱ in its `i`-th input with the other inputs fixed. -/
theorem descriptor_deriv (d : Descriptor) (hd : d.Nonsingular) (y : Fin d.n → ℝ)
    (hy : ∀ j, 1 ≤ y j) (i : Fin d.n) :
    HasDerivAt (fun z => d.value (Function.update y i z))
      (if d.label i = .NEQ then d.value y * (d.value y - 1) / (y i * (y i + 1))
        else -(d.value y * (d.value y - 1)) / (y i + 1)) (y i) := by sorry

end ReadTwiceCount
