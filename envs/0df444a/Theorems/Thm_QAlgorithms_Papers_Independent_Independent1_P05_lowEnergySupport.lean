-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_lowEnergySupport
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.lowEnergySupport
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:34:53.161985+00:00
-- url     : https://prove2.me/theorems/4bb30def-8678-4aff-9b2e-e33e13043940
-- title:
--   Section 2: support of both measurement distributions
-- statement:
--   Let $H_X,H_Z$ be a binary CSS check presentation with $n,m_x,m_z>0$, and let $\rho$ be any density operator with $\operatorname{Tr}(H\rho)\le\epsilon n$, where $\epsilon\ge0$ and $H$ is the sum of the actual check projectors. Write $D_z,D_x$ for its standard- and product-Hadamard-basis distributions and $G_b^\delta$ for the words violating at most a $\delta$ fraction of the actual checks on side $b$. For every $\epsilon_1>0$,
--   $$
--   D_z(G_z^{\epsilon_1})\ge1-\frac{\epsilon n}{\epsilon_1m_z},
--   \qquad D_x(G_x^{\epsilon_1})\ge1-\frac{\epsilon n}{\epsilon_1m_x}.
--   $$
--   If $\epsilon=0$, both $G_z^0$ and $G_x^0$ have probability one. If $\epsilon>0$, choosing $\epsilon_1=200n\epsilon/\min(m_x,m_z)$ gives both masses at least $199/200$.
--
--   These bounds place low-energy measurement outcomes in the approximate classical codes. The energy identity and probability bounds are conclusions of the source argument, not hypotheses of the formal statement.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Section 2: support of both measurement distributions, PDF p. 3. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

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




























/-- Section 2, PDF pp.3--4: both support bounds, the zero-energy case, and the
199/200 specialization. No energy identity or concentration conclusion is assumed. -/
theorem lowEnergySupport {n mx mz : ℕ} (C : CheckPresentation n mx mz)
    (hn : 0 < n) (hmx : 0 < mx) (hmz : 0 < mz)
    (rho : Matrix (Qubits n) (Qubits n) ℂ) (hrho : IsDensityMatrix rho)
    (eps : ℝ) (heps : 0 ≤ eps)
    (henergy : (NLTS.cssCheckHamiltonian C*rho).trace.re ≤ eps*n) :
    (∀ eps1 : ℝ, 0 < eps1 →
      nltsMass rho false (nltsApprox C false eps1) ≥ 1-eps*n/(eps1*mz) ∧
      nltsMass rho true (nltsApprox C true eps1) ≥ 1-eps*n/(eps1*mx)) ∧
    (eps = 0 → nltsMass rho false (nltsApprox C false 0) = 1 ∧
      nltsMass rho true (nltsApprox C true 0) = 1) ∧
    (0 < eps → let eps1 := 200*(n : ℝ)*eps/(min mx mz : ℕ)
      nltsMass rho false (nltsApprox C false eps1) ≥ 199/200 ∧
      nltsMass rho true (nltsApprox C true eps1) ≥ 199/200) := by sorry








end QAlgorithms.Papers.Independent.Independent1.P05
