-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_squeezing_schmidt
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.squeezing_schmidt
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:16:58.892985+00:00
-- url     : https://prove2.me/theorems/ee79750c-4e58-4bca-89f9-04b04e7d6c2a
-- title:
--   Appendix 3: normalized squeezing outputs and Schmidt weights
-- statement:
--   Let $0\le\lambda<1$, put $G=(1-\lambda^2)^{-1}$, and let $V_\lambda$ be the physical vacuum-environment amplifier isometry, with system mode first. Its Kraus components are those of the quantum-limited amplifier of intensity gain $G$. For every nonnegative integer $k$, its output $|\Psi_\lambda^{(k)}\rangle=V_\lambda|k\rangle$ has norm one and the Schmidt expansion
--
--   $$
--   |\Psi_\lambda^{(k)}\rangle=\sum_{n=0}^{\infty}\sqrt{p_n^{(k)}(\lambda)}\,|n+k,n\rangle,
--   \qquad p_n^{(k)}(\lambda)=(1-\lambda^2)^{k+1}\lambda^{2n}\binom{n+k}{n}.
--   $$
--
--   These nonnegative weights sum to one. The series converges in Hilbert norm, and every coefficient outside $a=b+k$ is zero. For arbitrary Fock vectors $u=\sum_k u_k|k\rangle$, one has $V_\lambda u=\sum_k u_k|\Psi_\lambda^{(k)}\rangle$ in Hilbert norm. For normalized $u$, the actual partial trace of this vector is a density operator and equals $A_G(|u\rangle\langle u|)$. If $\lambda=\tanh r$ with $r\ge0$, then $G=\cosh^2r$.
--
--   This identifies the physical dilation with its squared Schmidt law. The appendix positive-phase convention corrects the sign and factor in the printed exponential (6); the weights are indexed and need not be decreasing.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 6, (10)–(12), (A.4)–(A.18)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF pp.3,5-6, (10)-(12),(A.4)-(A.18). The physical
amplifier isometry has the normalized positive Schmidt expansion, and extends
linearly to arbitrary inputs. Eq.(6)'s exp[r(aa-a†a†)/2] is corrected to the
positive convention exp[r(a†a†-aa)] agreeing with the appendix and lambda=tanh r.
The indexed probabilities need not be decreasing. -/
theorem squeezing_schmidt (lambda : ℝ) (hl : 0 ≤ lambda) (hlu : lambda < 1) :
    D.AmplifierRealized (Real.sqrt (intensityGain lambda)) ∧
    Isometry (squeezing lambda) ∧
    (∀ u : D.Fock, ∀ a b : ℕ,
      squeezing lambda u (a, b) = D.amplifierKraus (Real.sqrt (intensityGain lambda)) b u a) ∧
    (∀ k : ℕ, ProbabilityLaw (fockSchmidtWeight k lambda) ∧ ‖squeezed k lambda‖ = 1 ∧
      HasSum (fun n => (Real.sqrt (fockSchmidtWeight k lambda n) : ℂ) • D.bipartiteKet (n + k, n))
        (squeezed k lambda) ∧
      ∀ a b : ℕ, squeezed k lambda (a, b) =
        if a = b + k then (Real.sqrt (fockSchmidtWeight k lambda b) : ℂ) else 0) ∧
    (∀ u : D.Fock, HasSum (fun k => u k • squeezed k lambda) (squeezing lambda u)) ∧
    (∀ u : D.Fock, ‖u‖ = 1 →
      D.IsDensity (firstMarginal (squeezing lambda u)) ∧
      D.HasFockMatrix (firstMarginal (squeezing lambda u))
        (fun a c => ∑' b : ℕ, squeezing lambda u (a, b) * star (squeezing lambda u (c, b))) ∧
      firstMarginal (squeezing lambda u) = C.amplifier (intensityGain lambda) (C.pureState u)) ∧
    (∀ r : ℝ, 0 ≤ r → lambda = Real.tanh r → intensityGain lambda = Real.cosh r ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
