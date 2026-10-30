-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_pauli_binomial_spectrum
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.pauli_binomial_spectrum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:35:43.172987+00:00
-- url     : https://prove2.me/theorems/24127d35-1f3f-4a9d-bb71-3b7c05ff367e
-- title:
--   Exact Pauli/binomial information spectrum
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. For the Pauli example let $0\le p<1/2$ and $0\le\varepsilon<1$. The nontrivial NS arrays are $P=(p/2,p/2,(1-p)/2,(1-p)/2)$ and $Q=(p^2,p^2,(1-p)^2,(1-p)^2)$. Additional zero-$P$ entries do not affect the spectrum; the reference is not normalized here. For $p>0$, define $F(k-1;n,p)=\Pr[\operatorname{Bin}(n,p)<k]$ with $F(-1)=0$, and $k_* =\max\{0\le k\le n:F(k-1;n,p)\le\varepsilon\}$. Then
--   $$D_s^\varepsilon(P^{\otimes n}\Vert Q^{\otimes n})=k_*\log\frac{1-p}{p}+n\log\frac1{2(1-p)}.$$
--   At $p=0$ the spectrum is $-n$. For $n=1$, the cutoff changes from $0$ to $1$ at $\varepsilon=1-p$. The formula permits exact finite-block evaluation.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 25, Appendix A: exact Pauli/binomial spectrum

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Appendix A, PDF pp.24--25: exact spectrum with strict positive-p branch and
p=0 treated separately. For n=1 the atom boundary is epsilon=1-p, as follows
from the displayed Bernoulli rescaling (the plan's epsilon=p check was incorrect). -/
theorem pauli_binomial_spectrum (p e : ℝ) (hp : 0 ≤ p ∧ p < 1/2)
    (he : 0 ≤ e ∧ e < 1) (n : ℕ) :
    (p = 0 → classicalSpectrumDivergence e (weightPower n (pauliP p)) (weightPower n (pauliQ p)) =
      ((-(n : ℝ) : ℝ) : EReal)) ∧
    (0 < p → classicalSpectrumDivergence e (weightPower n (pauliP p)) (weightPower n (pauliQ p)) =
      (((binomialCutoff n p e : ℝ)*logTwo ((1-p)/p) +
        n*logTwo (1/(2*(1-p))) : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
