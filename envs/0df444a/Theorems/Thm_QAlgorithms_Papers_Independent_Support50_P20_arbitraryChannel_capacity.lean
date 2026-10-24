-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P20_arbitraryChannel_capacity
-- name    : QAlgorithms.Papers.Independent.Support50.P20.arbitraryChannel_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:35:40.314547+00:00
-- url     : https://prove2.me/theorems/f2d16f54-0b4d-496e-9de1-6ab901a9c61e
-- title:
--   Capacity of an arbitrary channel sequence
-- statement:
--   Fix a complex output Hilbert space $B$. For each positive integer $n$, let $W_n:x_n\mapsto\rho_{x_n}^{(n)}$ be an arbitrary channel from a nonempty set $X_n$ to normalized trace-class states on the completed tensor product $B^{\otimes n}$. No relation between different blocklengths is assumed, and $X_n$ may include entangled block preparations. Define $C$ independently as the extended supremum of $\liminf_{n\to\infty}\log_2(m_n)/n$ over sequences of actual $m_n$-message codes whose average errors tend to zero. For each discrete law $P$ on $X_n$, form $\pi_{n,P}^{A_nB^{\otimes n}}=\sum_{x_n}P(x_n)|x_n\rangle\langle x_n|\otimes\rho_{x_n}^{(n)}$ and its marginals. Then the following outer limit exists, possibly with value $+\infty$, and
--
--   $$
--   C=\lim_{\epsilon\downarrow0}\liminf_{n\to\infty}\frac1n\sup_P D_H^\epsilon\bigl(\pi_{n,P}^{A_nB^{\otimes n}}\|\pi_{n,P}^{A_n}\otimes\pi_{n,P}^{B^{\otimes n}}\bigr).
--   $$
--
--   This operational formula covers channel sequences without causality, memorylessness, or stationarity. The small-error limit is taken after the lower limit in blocklength.
--
--   **Formalization Note** Completed tensor powers use square-summable coordinates indexed by tensor-product basis tuples. Sequence index zero denotes the one-use channel, so every blocklength denominator is positive. The equality with the outer limit is expressed as convergence to the independently defined operational capacity.
-- source:
--   One-Shot Classical-Quantum Capacity and Hypothesis Testing, arXiv:1007.5456v3, PDF p. 4, Unnumbered main asymptotic result, (10): arbitrary-channel sequence capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P20

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P20

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass IsPositive operatorTrace State)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF pp.4–5, (10) and footnote [23]: arbitrary-channel sequence capacity.
The inner limit is liminf; epsilon decreases to zero AFTER it. Output coordinates
are those of B tensor (n+1), and inputs X_n are unrestricted block preparations.
The Tendsto formulation retains the outer limit and its existence, even at infinity. -/
theorem arbitraryChannel_capacity {I : Type*} [Nonempty I] {X : ℕ → Type*}
    [∀ n, Nonempty (X n)] (W : ∀ n, ClassicalInputChannel (X n) (blockBasis I n)) :
    Tendsto
      (fun epsilon : ℝ => Filter.liminf
        (fun n => optimizedTestingInformation (blockBasis I n) (W n) epsilon /
          (((n + 1 : ℕ) : ℝ) : EReal)) atTop)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (vanishingErrorCapacity W)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P20

end
