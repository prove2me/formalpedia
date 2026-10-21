-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_collective_phase_flip_capacity
-- name    : QAlgorithms.Papers.Independent.Next46.P40.collective_phase_flip_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:57:06.793304+00:00
-- url     : https://prove2.me/theorems/daceec34-f741-4060-9c82-1e84ee0e3c5d
-- title:
--   Collective phase-flip EA capacity region
-- statement:
--   Let $d\ge2$ and let $p=(p_0,\ldots,p_{d-1})$ be a probability distribution. Define $Z_k|j\rangle=e^{2\pi i jk/d}|j\rangle$ and the channel on two $d$-dimensional inputs by $\mathcal M_p(X)=\sum_k p_k(Z_k\otimes Z_k)X(Z_k\otimes Z_k)^\dagger$. Its output has dimension $d^2$. With independent sender–receiver entanglement and maximum joint error, its classical capacity region is exactly
--
--   $$C_E(\mathcal M_p)=\{(R_1,R_2)\in\mathbb R_{\ge0}^2:\ R_1\le2\log_2d,\ R_2\le2\log_2d,\ R_1+R_2\le4\log_2d-H(p)\}.$$
--
--   Here $H(p)=-\sum_k p_k\log_2p_k$, with zero terms equal to zero. This example gives a full single-letter capacity region, including both individual bounds.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 9, §IV, (59)–(60)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Next46.P40

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation marginalRB associate)

variable {A B C E R S : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype R] [Fintype S]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

variable [DecidableEq R] [DecidableEq S]

/-- PDF pp.9--10, (59)--(60): both individual bounds and the sum bound.
The d=1 case is excluded as in the source. -/
theorem collective_phase_flip_capacity
    (d : ℕ) (hd : 2 ≤ d) (p : Fin d → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hpsum : ∑ k, p k = 1) :
    eaMacCapacityRegion (collectivePhaseFlip p) =
      {r : ℝ × ℝ | 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
        r.1 ≤ 2 * Real.logb 2 (d : ℝ) ∧ r.2 ≤ 2 * Real.logb 2 (d : ℝ) ∧
        r.1 + r.2 ≤ 4 * Real.logb 2 (d : ℝ) - shannonBits p} := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
