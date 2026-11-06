-- Prove2me | Theorems.Thm_RandomLPIPM_eq_2
-- name    : RandomLPIPM.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:11:36.890965+00:00
-- url     : https://prove2.me/theorems/7eb8ee3c-303c-4eee-a511-3369c9aa4e0d
-- title:
--   Eq. (2) — $d\log x_\mu/d\log\mu=(I-P(AX_\mu))\mathbf 1$ and $d\log s_\mu/d\log\mu=P(AX_\mu)\mathbf 1$
-- statement:
--   Let $A\in\mathbb R^{d\times n}$ and $\mu>0$, and let $(x_\mu,s_\mu)$ be the central path of LP(A). Then the central path is differentiable in $\log\mu$ and its relative rates of change are the components of $\mathbf 1_n$ in the orthogonal decomposition $\mathbb R^n=\ker[AX_\mu]\oplus\operatorname{im}[(AX_\mu)^\top]$:
--   $$\frac{d\log x_\mu}{d\log\mu}=(I-P(AX_\mu))\mathbf 1_n,\qquad \frac{d\log s_\mu}{d\log\mu}=P(AX_\mu)\mathbf 1_n .$$
--   Here, coordinatewise, $\frac{d\log x_{\mu,i}}{d\log\mu}$ is the derivative of $t\mapsto\log x_{e^t,i}$ at $t=\log\mu$.
--
--   These identities turn the iteration complexity of path following into a question about the $\ell_\infty$ norm of a projection of the all-ones vector.
--
--   Differences from the source:
--   - generalization: LP(A) for the Gaussian A of Section 1, P(M) := Mᵀ(MMᵀ)⁻¹M → every real matrix A, P(M) the orthogonal projector onto the row space of M; reason: the derivation on pp.6–7 uses only the central path equations; for full-row-rank A (almost surely for Gaussian A) the projector equals the printed formula
--   - encoding: d log x_μ / d log μ (assumed to exist, p.7) → HasDerivAt of t ↦ log x_{e^t, i} at t = log μ, coordinatewise; reason: asserts differentiability instead of using a junk-valued derivative
--   - encoding: (x_μ, s_μ) the solution of the central path equations → x_μ the log-barrier minimizer, s_μ = μ/x_μ; reason: equivalent by p.22
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), display (2), p.7

import Mathlib
import Definitions.Def_RandomLPIPM_xMu
import Definitions.Def_RandomLPIPM_sMu
import Definitions.Def_RandomLPIPM_projRow

open Matrix

namespace RandomLPIPM

/-- **Eq. (2): the logarithmic derivatives of the central path.** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), display (2), p.7.

For every `A ∈ ℝ^{d×n}` and `μ > 0`, the central path of LP(A) satisfies
`d log x_μ / d log μ = (I − P(AX_μ))1` and `d log s_μ / d log μ = P(AX_μ)1`.

**Formalization Note.** The derivatives are taken coordinatewise in `t = log μ` and asserted with
`HasDerivAt`, so the statement also asserts differentiability. No full-row-rank hypothesis is
printed (the derivation on pp.6–7 uses only the central path equations), and none is added. -/
theorem eq_2 {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (μ : ℝ) (hμ : 0 < μ) (i : Fin n) :
    HasDerivAt (fun t => Real.log (xMu A (Real.exp t) i))
        ((1 - projRow (A * diagonal (xMu A μ)) 1) i) (Real.log μ) ∧
      HasDerivAt (fun t => Real.log (sMu A (Real.exp t) i))
        (projRow (A * diagonal (xMu A μ)) 1 i) (Real.log μ) := by sorry

end RandomLPIPM
