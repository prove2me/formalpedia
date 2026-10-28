-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_fock_majorization_chain
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.fock_majorization_chain
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T04:17:49.211795+00:00
-- url     : https://prove2.me/theorems/bcbc8970-8c39-4329-9c2f-2a90319a7113
-- title:
--   Fock input majorization chain, Eqs.(13)–(14), Appendix 4a–b
-- statement:
--   Let $0\le\lambda<1$, and let $p^{(k)}(\lambda)$ be the normalized squared Schmidt law $p_n^{(k)}=(1-\lambda^2)^{k+1}\lambda^{2n}\binom{n+k}{n}$ for input number state $|k\rangle$. For every nonnegative increment $d$, the kernel $D^{(d)}$ is the identity if $d=0$, and, if $d\ge1$, is
--
--   $$
--   D^{(d)}_{nm}=\begin{cases}(1-\lambda^2)^d\binom{n-m+d-1}{d-1}\lambda^{2(n-m)},&m\le n,\\0,&m>n.\end{cases}
--   $$
--
--   It has nonnegative entries, column sums one, and row sums at most one, with convergent sums. For every $k\ge0$,
--
--   $$
--   p^{(k+d)}(\lambda)=D^{(d)}p^{(k)}(\lambda),\qquad
--   p^{(k)}(\lambda)\succ p^{(k+d)}(\lambda).
--   $$
--
--   The single-step kernel is $D^{(1)}_{nm}=(1-\lambda^2)\lambda^{2(n-m)}$ for $m\le n$, and zero otherwise. In particular $p^{(0)}(\lambda)\succ p^{(k)}(\lambda)$ for every $k$. Majorization compares decreasing partial sums, independently of photon-index order.
--
--   This proves the vacuum majorization conjecture for all Fock inputs. In (A.27), the printed upper binomial index $m+d-1$ is replaced by $n-m+d-1$, as forced by the matrix powers in (A.25).
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 3, (13)–(14), Appendix 4a–b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF pp.3,6-7, (13)-(14),(A.19)-(A.27). The single
step and every increment have an explicit stochastic witness. A.27's printed
choose(m+d-1,d-1) is corrected to choose(n-m+d-1,d-1), forced by A.25 and
its displayed matrix powers; for d=2 column zero begins 1,2,3 before powers. -/
theorem fock_majorization_chain (lambda : ℝ) (hl : 0 ≤ lambda) (hlu : lambda < 1) :
    (∀ n m : ℕ, fockKernel 1 lambda n m =
      if m ≤ n then (1 - lambda ^ 2) * lambda ^ (2 * (n - m)) else 0) ∧
    (∀ d : ℕ, CountableSubunitalStochastic (fockKernel d lambda) ∧
      ∀ k : ℕ, ProbabilityMajorizes (fockSchmidtWeight k lambda) (fockSchmidtWeight (k + d) lambda) ∧
        ∀ n : ℕ, HasSum (fun m => fockKernel d lambda n m * fockSchmidtWeight k lambda m)
          (fockSchmidtWeight (k + d) lambda n)) ∧
    (∀ k : ℕ, ProbabilityMajorizes (fockSchmidtWeight 0 lambda) (fockSchmidtWeight k lambda)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
