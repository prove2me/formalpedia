-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P90_bb84_bellFamily
-- name    : QAlgorithms.Papers.Independent.Intake100.P90.bb84_bellFamily
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:11:08.752628+00:00
-- url     : https://prove2.me/theorems/0d8e5344-6175-4abc-9b82-14e1eb4bf27e
-- title:
--   Forward BB84 Bell-diagonal family with physical coefficients
-- statement:
--   For any normalized two-qubit input $\rho$, form the BB84 equal-basis average $\mathcal D_1(\rho)=\frac12[\rho+(H\otimes H)\rho(H\otimes H)^\dagger]$, followed by the uniform bilateral Pauli average $\sigma=\mathcal D_2(\mathcal D_1(\rho))$. Let $Q$ be its computational-basis disagreement probability. The output is a normalized density matrix, $0\le Q\le1$, and there exists $t$ such that
--
--   $$0\le t\le\min(Q,1-Q),\qquad \sigma=(1-Q-t)P_{\Phi^+}+tP_{\Phi^-}+tP_{\Psi^+}+(Q-t)P_{\Psi^-}.$$
--
--   On the conventional branch $Q\le1/2$, the parameter interval reduces to the printed $0\le t\le Q$. This forward representation reduces the input state's parameters; it makes no converse assertion that every $t$ is achieved by a prescribed attack.
--
--   **Formalization Note** The free source parameter $\lambda_1$ is called $t$. Nonnegativity of $1-Q-t$ requires $t\le1-Q$. The plan's proposed extension $\max(0,2Q-1)\le t\le Q$ is incorrect; the singlet at $Q=1,t=0$ is a counterexample to that extension.
-- source:
--   Lower and upper bounds on the secret key rate for QKD protocols using one--way classical communication, arXiv:quant-ph/0410215v2, PDF p. 4, Unnumbered BB84 Bell-diagonal family

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P90

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intake100.P90

/-- PDF p.4: forward family representation after BB84 D1 then D2, with Q
computed from the actual output. Physical coefficients are all nonnegative;
on the conventional Q<=1/2 branch the extra lower bound is automatic.
The source's free parameter lambda_1 is renamed t to avoid confusing it
with the first Bell weight. No claim that every parameter is attainable. -/
theorem bb84_bellFamily (rho : PairOp) (hrho : IsDensityMatrix rho) :
    let sigma := pairTwirl (bb84BasisAverage rho)
    let Q := sourceZDisagreement sigma
    IsDensityMatrix sigma ∧ 0 ≤ Q ∧ Q ≤ 1 ∧
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ min Q (1 - Q) ∧
      sigma = sourceBellDiagonal ![1 - Q - t, t, t, Q - t] := by sorry

end QAlgorithms.Papers.Independent.Intake100.P90

end
