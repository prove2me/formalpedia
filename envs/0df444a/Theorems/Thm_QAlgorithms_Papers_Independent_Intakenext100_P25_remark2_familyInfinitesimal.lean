-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P25_remark2_familyInfinitesimal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P25.remark2_familyInfinitesimal
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:27:42.289405+00:00
-- url     : https://prove2.me/theorems/8e18eb09-1bec-4c72-b7fe-1525474de201
-- title:
--   Remark 2: component bounds and the finite-family converse
-- statement:
--   Let $G$ be a densely defined positive self-adjoint operator on a separable infinite-dimensional complex Hilbert space $H_A$, with spectral bottom zero. Let $H_B$ be another such Hilbert space. Let $K$ be a finite or countable index set, and let $V_k:D(\sqrt G)\to H_B$ be $\sqrt G$-bounded linear operators. For $E>0$, write $\|V_k\|_E^G$ for the operator E-norm in (9), and put
--
--   $$
--   M(E)=\sup_{\rho\in\mathfrak S(H_A),\,\operatorname{Tr}G\rho\le E}\sum_{k\in K}\operatorname{Tr}V_k\rho V_k^*.
--   $$
--
--   This is a sum of traces, without a square root, and it may be infinite for a general countable family. Then
--
--   $$
--   \|V_k\|_E^G\le\sqrt{M(E)}\qquad(k\in K,\ E>0).
--   $$
--
--   If $M(E)=o(E)$ as $E\to\infty$, every $V_k$ is $\sqrt G$-infinitesimal. Conversely, if $K$ is finite and every $V_k$ is $\sqrt G$-infinitesimal, then $M(E)=o(E)$.
--
--   The result distinguishes aggregate control of an infinite Kraus family from infinitesimality of its individual members. No converse for arbitrary countable families is asserted.
--
--   **Formalization Note** The operator E-norm is evaluated using the equivalent countable-ensemble formula (11). Nonnegative sums and suprema take values in the extended nonnegative reals, so divergence is retained. The operator acts only on $D(\sqrt G)$; no adjoint or closability of $V_k$ is required.
-- source:
--   On completion of the cone of CP linear maps with respect to the energy-constrained diamond norm, arXiv:1810.10922v2, PDF p. 17, Remark 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P25

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakenext100.P25

open QAlgorithms.RealRegisters (Hilbert)

/-- Shirokov, arXiv:1810.10922v2, PDF p.17, Remark 2. Sublinear aggregate
mass forces every member to be infinitesimal and gives the stated square-root
bound. The converse is asserted only for a finite family. -/
theorem remark2_familyInfinitesimal {K : Type*} [Countable K]
    (G : EnergyObservable) (V : K → (G.root.domain →ₗ[ℂ] Hilbert ℕ))
    (hV : ∀ k : K, RelativelyBounded G (V k)) :
    (∀ (k : K) (E : ℝ), 0 < E →
      operatorEnergyNorm G (V k) E ≤ (familyEnergyMass G V E) ^ (1 / 2 : ℝ)) ∧
    (FamilySublinear G V → ∀ k : K, SqrtEnergyInfinitesimal G (V k)) ∧
    (Finite K → (∀ k : K, SqrtEnergyInfinitesimal G (V k)) → FamilySublinear G V) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P25

end
