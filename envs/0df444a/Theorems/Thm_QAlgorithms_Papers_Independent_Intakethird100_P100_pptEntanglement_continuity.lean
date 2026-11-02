-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P100_pptEntanglement_continuity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P100.pptEntanglement_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:25:41.037515+00:00
-- url     : https://prove2.me/theorems/ab36bde6-8888-48ca-a938-99c2177ad8cc
-- title:
--   Continuity of the normalized PPT relative-entropy infimum
-- statement:
--   Let $H_A,H_B$ have positive finite dimensions and set $N=\dim(H_A\otimes H_B)$. Let $\mathrm{PPT}$ be exactly the trace-one positive semidefinite bipartite matrices whose partial transpose is positive semidefinite. Define $E_{\mathrm{PPT}}(\omega)=\inf_{\tau\in\mathrm{PPT}}S(\omega\Vert\tau)$, retaining infinity at a support violation.
--
--   All logarithms are natural. States are positive semidefinite matrices of trace one, and the distance $t=\|\sigma-\rho\|_1$ uses the full trace norm, without a factor of one half. Set $\eta(t)=-t\log t$, with $\eta(0)=0$.
--
--   For arbitrary bipartite density matrices $\sigma,\rho$ with $t\leq 1/3$, both infima are finite and
--
--   $$
--   |E_{\mathrm{PPT}}(\sigma)-E_{\mathrm{PPT}}(\rho)|\leq 2\bigl(t\log N+\eta(t)\bigr)+4t.
--   $$
--
--   This is the paper's normalized PPT variation. Neither input is required to be PPT.
--
--   **Formalization Note** The accepted entropy infimum is stored in bits. The Lean bound multiplies its absolute real difference by $\log 2$, which gives exactly the natural-logarithm quantity displayed above.
-- source:
--   Continuity of Relative Entropy of Entanglement, arXiv:quant-ph/9910002v1, PDF p. 2, Remark (i), with the introductory variation on p.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P100

noncomputable section

open Filter

open scoped ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P100

open QAlgorithms.Papers.Independent.Dependency50.P15
  (relativeDistance relativeDistanceValue positiveOperatorRelativeEntropyBits groupedTensorPower)

open QAlgorithms.Papers.Independent.Information100.P54
  (relativeEntropyBits relativeEntanglement)

/-- Remark (i), PDF p.2, and introduction, PDF p.1: the identical bound (3)
for minimization over normalized PPT states, with arbitrary density inputs. -/
theorem pptEntanglement_continuity
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (sigma rho : Matrix (A × B) (A × B) ℂ)
    (hsigma : IsDensityMatrix sigma) (hrho : IsDensityMatrix rho)
    (hclose : traceNorm (sigma - rho) ≤ 1 / 3) :
    pptEntanglement sigma < ⊤ ∧ pptEntanglement rho < ⊤ ∧
    Real.log 2 * |(pptEntanglement sigma).toReal -
      (pptEntanglement rho).toReal| ≤
      2 * (traceNorm (sigma - rho) * Real.log (Fintype.card (A × B)) +
        Real.negMulLog (traceNorm (sigma - rho))) + 4 * traceNorm (sigma - rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P100

end
