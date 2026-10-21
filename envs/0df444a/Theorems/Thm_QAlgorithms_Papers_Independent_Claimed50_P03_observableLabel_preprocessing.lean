-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_observableLabel_preprocessing
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.observableLabel_preprocessing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:02:37.542953+00:00
-- url     : https://prove2.me/theorems/7f765ae6-af9c-4344-9d16-1c058ec7c087
-- title:
--   Appendix E.1, Eq.(E10): classical output-label construction
-- statement:
--   A randomized Pauli shot chooses each wire's axis uniformly from $X,Y,Z$ and then records its Born-distributed eigenvalue. Its inverse snapshot is $\widehat\rho=\bigotimes_i(3|s_i\rangle\langle s_i|-I)$. Shots are independent. The uncentered shadow norm is $\|O\|_{\rm sh}=\sup_{\sigma\text{ density}}(\mathbb E_\sigma[\operatorname{tr}(O\widehat\rho)^2])^{1/2}$.
--
--   Fix output locality $\kappa\ge1$ and participation $d\ge1$. Let $n,N\ge1$, and let $O=\sum_{a=1}^t c_aQ_a$ be supplied as a canonical sparse Pauli description: all $c_a\ne0$, the words are distinct, each word has at most $\kappa$ distinct nonidentity wires, and $O$ has a $(\kappa,d)$ decomposition. The implemented loop, for each recorded output shot $s_\ell$, computes exactly
--   $$y_\ell(O)=\sum_{a=1}^tc_a\operatorname{tr}(Q_a\widehat\rho(s_\ell))=\operatorname{tr}(O\widehat\rho(s_\ell)).$$
--   Its charged arithmetic/access cost is at most $[(5\kappa+3)t+1]N$, including allocation of the cached label array, and at most $C_{\kappa,d}nN$ for a constant independent of $n,N,O$ and the data. This is output-label preprocessing only.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 47, Appendix E.1, Eq.(E10): classical output-label construction

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Appendix E.1, paper p.47, E10: concrete sparse output-label preprocessing,
including the O(kap t N) support/access cost and the O_{kap,d}(nN) specialization. -/
theorem observableLabel_preprocessing :
    ∀ (kap d : ℕ), 1 ≤ kap → 1 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (n N : ℕ), 1 ≤ n → 1 ≤ N → ∀ terms : SparseObservable n,
      ValidDescription kap terms → HasBoundedDegree kap d (decodeObservable terms) →
      ∀ data : Fin N → Shot n,
        (runLabels terms data).value = ((List.finRange N).map
          (fun l => effectProb (decodeObservable terms) (pauliSnapshot (data l)))).toArray ∧
        (runLabels terms data).steps ≤ (5 * kap + 3) * terms.length * N + N ∧
        ((runLabels terms data).steps : ℝ) ≤ C * (n : ℝ) * (N : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
