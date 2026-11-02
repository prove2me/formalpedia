-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P100_relativeEntanglement_continuity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P100.relativeEntanglement_continuity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:24:12.600958+00:00
-- url     : https://prove2.me/theorems/1fd0f384-1b3c-43f0-96aa-110adfac4d46
-- title:
--   Quantitative continuity of relative entropy of entanglement
-- statement:
--   Let $H_A,H_B$ be fixed complex Hilbert spaces of positive finite dimensions, and let $N=\dim(H_A\otimes H_B)$. For a bipartite state $\omega$, define $E_r(\omega)=\inf_{\tau\in\mathrm{SEP}}S(\omega\Vert\tau)$, where $\mathrm{SEP}$ consists exactly of finite convex combinations of product density matrices and $S$ is Umegaki relative entropy, infinite when support inclusion fails.
--
--   All logarithms are natural. States are positive semidefinite matrices of trace one, and the distance $t=\|\sigma-\rho\|_1$ uses the full trace norm, without a factor of one half. Set $\eta(t)=-t\log t$, with $\eta(0)=0$.
--
--   For any states $\sigma,\rho$ with $t\leq 1/3$, both entanglement values are finite and
--
--   $$
--   |E_r(\sigma)-E_r(\rho)|\leq 2\bigl(t\log N+\eta(t)\bigr)+4t.
--   $$
--
--   This is the precise separable-state specialization of the paper's Fannes-type continuity requirement. No separability assumption is imposed on either input.
--
--   **Formalization Note** The accepted entropy infimum is stored in bits. The Lean bound multiplies its absolute real difference by $\log 2$, which gives exactly the natural-logarithm quantity displayed above.
-- source:
--   Continuity of Relative Entropy of Entanglement, arXiv:quant-ph/9910002v1, PDF p. 1, Introduction (2); specialization of (3) through Remark (i), p.2

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

/-- Introduction (2), PDF p.1, specialized via Remark (i), PDF p.2:
relative entropy of entanglement obeys the exact quantitative bound (3).
The local domain t <= 1/3 is retained. No separability of the inputs is assumed. -/
theorem relativeEntanglement_continuity
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (sigma rho : Matrix (A × B) (A × B) ℂ)
    (hsigma : IsDensityMatrix sigma) (hrho : IsDensityMatrix rho)
    (hclose : traceNorm (sigma - rho) ≤ 1 / 3) :
    relativeEntanglement sigma < ⊤ ∧ relativeEntanglement rho < ⊤ ∧
    Real.log 2 * |(relativeEntanglement sigma).toReal -
      (relativeEntanglement rho).toReal| ≤
      2 * (traceNorm (sigma - rho) * Real.log (Fintype.card (A × B)) +
        Real.negMulLog (traceNorm (sigma - rho))) + 4 * traceNorm (sigma - rho) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P100

end
