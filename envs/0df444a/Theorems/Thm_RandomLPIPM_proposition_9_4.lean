-- Prove2me | Theorems.Thm_RandomLPIPM_proposition_9_4
-- name    : RandomLPIPM.proposition_9_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:20.714245+00:00
-- url     : https://prove2.me/theorems/b8de2fe7-d2fc-410c-9194-373d0d4da814
-- title:
--   Proposition 9.4 — $\Phi_{x,\mu}$ has a unique minimizer on $\ker(AX)$, equal to $(x(\mu)-x)/x$ when that is in the $\ell_\infty$ box
-- statement:
--   Consider (LP) with $A$ of full row rank and both programs strictly feasible, a strictly feasible $x$, and the quadratic extension $\tilde d$ at $\rho=1/4$. For any $\mu>0$:
--   1. $\Phi_{x,\mu}$ has a unique global minimizer on $\ker(AX)$;
--   2. if $u^*=(x(\mu)-x)/x$ satisfies $\|u^*\|_\infty\le1/4$, then $u^*\in\ker(AX)$ and $u^*$ is the global minimizer of $\Phi_{x,\mu}$ on $\ker(AX)$.
--
--   This is what lets Algorithm 1 re-center by minimizing a globally well-conditioned function: as long as the next central point is within a factor $1\pm1/4$ of the current iterate in every coordinate, the smoothed objective has the same minimizer as the log-barrier.
--
--   **Formalization Note** $u\in\ker(AX)$ is written $A(x\cdot u)=0$.
--
--   Differences from the source:
--   - encoding: u ∈ ker(AX) → A(x·u) = 0; reason: the same subspace
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Proposition 9.4, p.78 (proof p.82)

import Mathlib
import Definitions.Def_RandomLPIPM_IsPrimalStrictFeas
import Definitions.Def_RandomLPIPM_IsDualStrictFeas
import Definitions.Def_RandomLPIPM_centralX
import Definitions.Def_RandomLPIPM_phi
import Definitions.Def_ColumnRandLP_Norms

open Matrix

namespace RandomLPIPM

/-- **Proposition 9.4.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Proposition 9.4, p.78 (proof p.82).

Let `d̃` be the quadratic extension of `d` at `ρ = 1/4`. For (LP) and a strictly feasible `x`, and any
`μ > 0`, the function `Φ_{x,μ}` has a unique global minimizer in `ker(AX)`. If
`u* = (x(μ) − x)/x` satisfies `‖u*‖_∞ ≤ 1/4`, it is the global minimizer of `Φ_{x,μ}` in `ker(AX)`.

**Formalization Note.** The hypotheses are the standing assumptions of (LP) (p.4: `A` has full row rank, dual strictly feasible) and the strict feasibility of `x` (p.77), which also gives the primal
strict feasibility of (LP).
`u ∈ ker(AX)` is written `A(x·u) = 0`. -/
theorem proposition_9_4 {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ)
    (c : Fin n → ℝ) (hA : A.rank = d)
    (hD : ∃ y, IsDualStrictFeas A c y) (x : Fin n → ℝ) (hx : IsPrimalStrictFeas A b x)
    (μ : ℝ) (hμ : 0 < μ) :
    (∃! u : Fin n → ℝ, A *ᵥ (x * u) = 0 ∧
        ∀ v : Fin n → ℝ, A *ᵥ (x * v) = 0 → phi c x μ u ≤ phi c x μ v) ∧
      (ColumnRandLP.supNorm (fun i => (centralX A b c μ i - x i) / x i) ≤ 1 / 4 →
        A *ᵥ (x * fun i => (centralX A b c μ i - x i) / x i) = 0 ∧
        ∀ v : Fin n → ℝ, A *ᵥ (x * v) = 0 →
          phi c x μ (fun i => (centralX A b c μ i - x i) / x i) ≤ phi c x μ v) := by sorry

end RandomLPIPM
