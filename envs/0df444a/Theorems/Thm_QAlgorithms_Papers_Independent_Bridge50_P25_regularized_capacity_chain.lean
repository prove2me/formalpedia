-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_regularized_capacity_chain
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.regularized_capacity_chain
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:06:53.193218+00:00
-- url     : https://prove2.me/theorems/eead9db9-c194-4026-a92e-55e8df02edaa
-- title:
--   Corollary IV.1: regularized capacity chain
-- statement:
--   Let $T$ be a quantum channel between positive finite-dimensional matrix algebras. The positive-copy quotients of its max-relative entropy of entanglement converge. Writing their limit as $E_{\max}^{\infty}(T)$, the two-way assisted entanglement-generation capacity $Q_{\leftrightarrow}(T)$ and private-state generation capacity $P_{\leftrightarrow}(T)$ satisfy
--
--   $$E_{\max}^{\infty}(T)=\lim_{n\to\infty}\frac{E_{\max}(T^{\otimes n})}{n},\qquad Q_{\leftrightarrow}(T)\le P_{\leftrightarrow}(T)\le E_{\max}^{\infty}(T)\le E_{\max}(T).$$
--
--   Both capacities use separable initial states, finite local workspaces, actual channel uses, unrestricted two-way LOCC, half trace-norm error tending to zero, and convergent key-bit rates with channel uses tending to infinity.
--
--   This improves the unregularized upper bound. It makes no additional strong-converse assertion for the regularization.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 15, Corollary IV.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Corollary IV.1, PDF p.15: capacity chain and convergence of the computed
regularization. No additional regularized strong-converse claim is made. -/
theorem regularized_capacity_chain (T : Superop I J) (hT : IsChannel T) :
    Tendsto (maxQuotients T) atTop (nhds (regularizedEMax T)) ∧
    twoWayGenerationCapacity T false ≤ twoWayGenerationCapacity T true ∧ twoWayGenerationCapacity T true ≤ regularizedEMax T ∧
    regularizedEMax T ≤ channelEMax T := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
