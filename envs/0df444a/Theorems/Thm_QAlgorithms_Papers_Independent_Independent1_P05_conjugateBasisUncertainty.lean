-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_conjugateBasisUncertainty
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.conjugateBasisUncertainty
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T19:34:57.066269+00:00
-- url     : https://prove2.me/theorems/273c3bd5-810e-4de7-aa8f-5f9ae649f397
-- title:
--   Fact 3: uncertainty for subsets in conjugate bases
-- statement:
--   Let $\rho$ be any $n$-qubit density operator, and let $D_z,D_x$ be its standard- and product-Hadamard-basis measurement distributions. For all sets $S,T\subseteq\{0,1\}^n$,
--   $$
--   D_x(T)\le2\sqrt{1-D_z(S)}+\frac{|S||T|}{2^n}.
--   $$
--
--   This bounds concentration in conjugate bases and applies to mixed states. No positive-mass hypothesis on $S$ is required; empty sets and $n=0$ are allowed.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Fact 3: uncertainty for subsets in conjugate bases, PDF p. 4. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P05

open PresentedCSS































/-- Fact 3, PDF p.4 and Appendix A p.8. Mixed states and empty subsets are allowed. -/
theorem conjugateBasisUncertainty {n : ℕ} (rho : Matrix (Qubits n) (Qubits n) ℂ)
    (hrho : IsDensityMatrix rho) (S T : Finset (NLTSWord n)) :
    nltsMass rho true T ≤ 2*Real.sqrt (1-nltsMass rho false S) +
      (S.card : ℝ)*T.card/(2 : ℝ)^n := by sorry





end QAlgorithms.Papers.Independent.Independent1.P05
