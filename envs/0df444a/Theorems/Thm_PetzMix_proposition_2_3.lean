-- Prove2me | Theorems.Thm_PetzMix_proposition_2_3
-- name    : PetzMix.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:14:30.570554+00:00
-- url     : https://prove2.me/theorems/36294893-0fd3-4340-97b2-2cc72e20e44d
-- title:
--   Proposition 2.3 — dual form of the quantum $W_1$ norm
-- statement:
--   Let $X$ be a traceless Hermitian operator on the periodic chain of $n$ qudits. Then its quantum Wasserstein norm of order 1 equals the largest expectation difference detectable by observables of Lipschitz constant at most one:
--   $$
--   \|X\|_{W_1}=\sup\big\{\operatorname{tr}[AX]\;:\;A=A^\dagger,\ \|A\|_L\le1\big\}.
--   $$
--   Here $\|X\|_{W_1}=\tfrac12\inf\{\sum_i\|X_i\|_1: X=\sum_iX_i,\ X_i=X_i^\dagger,\ \operatorname{tr}_iX_i=0\}$ (Definition 2.1) and $\|A\|_L=\max_i\delta_i(A)$ (Definition 2.2).
--
--   This duality converts bounds on the oscillations of Heisenberg-evolved observables into bounds on $W_1$ distances; it is the bridge used in Proposition 3.2.
--
--   **Formalization Note** Both sides are in $[0,\infty]$; the right side is the supremum of $\max(\operatorname{tr}[AX],0)$, which equals the real supremum because $A=0$ is admissible and the admissible set is symmetric.
--
--   Differences from the source:
--   - generalization: a fixed finite local dimension d → every d ≥ 1; reason: d = 1 is the trivial one-dimensional site; every d of the paper is included
--   - encoding: sup of real numbers → supremum in ℝ≥0∞ of ENNReal.ofReal (tr[AX]); w1 valued in ℝ≥0∞; reason: the supremum is ≥ 0 (A = 0) and finite iff the set is bounded, so the values agree
-- source:
--   Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Proposition 2.3, (24), p.13 (cited from De Palma–Marvian–Trevisan–Lloyd [62, Proposition 9])

import Mathlib
import Definitions.Def_PetzMix_HasExtInfluence
import Definitions.Def_QDSGibbs_w1

open scoped Matrix ComplexOrder ENNReal

set_option autoImplicit false

namespace PetzMix

open QDSGibbs

/-- **Proposition 2.3 (Dual form)** (Kim, Rapid mixing of quantum spin chains at any finite temperature, arXiv:2610.01190 (held copy sha256 38ff48d0…), Proposition 2.3, (24), p.13; cited from [62,
Proposition 9]). For every traceless Hermitian operator `X` on the chain,
`‖X‖_{W1} = sup{ tr[AX] : A = A†, ‖A‖_L ≤ 1 }`.

**Formalization Note** `‖·‖_{W1}` is the public `QDSGibbs.w1` (Definition 2.1, valued in `ℝ≥0∞`),
`‖A‖_L` is `lip A` (Definition 2.2). The supremum is taken in `ℝ≥0∞` of `ofReal (tr[AX])`: the set
contains `A = 0` and is symmetric under `A ↦ −A`, so its supremum is nonnegative and the truncation
`ofReal` changes nothing; a finite `w1 X` forces the set to be bounded. -/
theorem proposition_2_3 (n d : ℕ) (hd : 1 ≤ d) (X : ChainOp n d) (hX : X.IsHermitian)
    (htr : X.trace = 0) :
    w1 X = ⨆ (A : ChainOp n d) (_ : A.IsHermitian ∧ lip A ≤ 1), ENNReal.ofReal (A * X).trace.re := by sorry

end PetzMix
