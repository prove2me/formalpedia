-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P40_gentle_coherent_measurement
-- name    : QAlgorithms.Papers.Independent.Next46.P40.gentle_coherent_measurement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:49:39.048384+00:00
-- url     : https://prove2.me/theorems/0223670b-5028-4b8a-8097-f30c8d1dc94e
-- title:
--   Gentle coherent measurement
-- statement:
--   Let $A,R$ be finite nonzero quantum registers and let $K\ge1$. For each $k\in\{0,\ldots,K-1\}$, let $\rho_k$ be a density operator on $A$ and let $|\phi_k\rangle^{RA}$ be a normalized purification. Let $\{\Lambda_k\}$ be one complete POVM on $A$, and suppose $\epsilon\ge0$ and $\operatorname{Tr}(\rho_k\Lambda_k)\ge1-\epsilon$ for every $k$. With $J$ the outcome register, there is one isometry $D:A\to AJ$, independent of $k$, such that
--
--   $$\left\|(\mathrm{id}_R\otimes D)(\phi_k)-\phi_k\otimes|k\rangle\langle k|_J\right\|_1\le\sqrt{8\epsilon}\qquad\text{for every }k.$$
--
--   Here pure vectors denote their rank-one density operators under a channel, and the norm is the full trace norm. The isometry is the source's explicit $D|a\rangle=\sum_j(\sqrt{\Lambda_j}|a\rangle)\otimes|j\rangle$. This form permits coherent outcome extraction while fixing the relative phases.
-- source:
--   Entanglement-Assisted Capacity of Quantum Multiple-Access Channels, arXiv:quant-ph/0511228v2, PDF p. 3, Lemma 1

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

/-- PDF p.3, Lemma 1 (including the explicit isometry from its proof).
The outcome set is nonempty and ONE complete POVM is used for all states. -/
theorem gentle_coherent_measurement
    [Nonempty A] [Nonempty R] (K : ℕ) (hK : 0 < K)
    (rho : Fin K → Matrix A A ℂ) (hrho : ∀ k, IsDensityMatrix (rho k))
    (L : Fin K → Matrix A A ℂ) (hL : IsPOVM L)
    (v : Fin K → EuclideanSpace ℂ (R × A))
    (hv : ∀ k, ‖v k‖ = 1) (hpur : ∀ k, traceLeft (pureDensity (v k)) = rho k)
    (eps : ℝ) (heps : 0 ≤ eps) (hsuccess : ∀ k, 1 - eps ≤ effectProb (L k) (rho k)) :
    ∃ D : Matrix (A × Fin K) A ℂ,
      D = coherentMeasurement L ∧ Dᴴ * D = 1 ∧
      ∀ k, traceNorm (pureDensity (measuredPurification D (v k)) -
        pureDensity (appendLabel (v k) k)) ≤ Real.sqrt (8 * eps) := by sorry

end QAlgorithms.Papers.Independent.Next46.P40

end
