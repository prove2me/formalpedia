-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P25_lemma7_uniqueSlice
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P25.lemma7_uniqueSlice
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:28:20.508181+00:00
-- url     : https://prove2.me/theorems/9a3ce242-7eae-405a-8846-6925bac050cc
-- title:
--   Lemma 7: the unique environment slice at every positive energy
-- statement:
--   Let $H_A$ and $H_B$ be separable infinite-dimensional complex Hilbert spaces, and let $H_E$ be a separable Hilbert space, possibly finite dimensional. Let $G$ be a densely defined positive self-adjoint operator on $H_A$ with spectral bottom zero. Suppose $V:D(\sqrt G)\to H_B\otimes H_E$ is $\sqrt G$-bounded, where the tensor product is completed, and let $\tau\in H_E$ satisfy $\|\tau\|=1$. There is a unique $\sqrt G$-bounded operator $V_\tau:D(\sqrt G)\to H_B$ such that
--
--   $$
--   \|V_\tau\|_E^G\le\|V\|_E^G\quad\text{for every }E>0,
--   \qquad
--   \langle\psi\otimes\tau,V\varphi\rangle=\langle\psi,V_\tau\varphi\rangle
--   \quad(\varphi\in D(\sqrt G),\ \psi\in H_B).
--   $$
--
--   Here $\|\cdot\|_E^G$ denotes the operator E-norm in (9), and inner products are conjugate linear in their first argument. The unique operator is independent of $E$; uniqueness means equality on $D(\sqrt G)$.
--
--   This result supplies environment components of representing operators while preserving their energy norm bounds.
--
--   **Formalization Note** Countable orthonormal coordinates identify the system spaces with $\ell^2(\mathbb N)$ and the environment with $\ell^2(K)$ for an arbitrary countable basis index set $K$. Their completed tensor product is $\ell^2(\mathbb N\times K)$. The energy observable is encoded by its positive self-adjoint square root.
-- source:
--   On completion of the cone of CP linear maps with respect to the energy-constrained diamond norm, arXiv:1810.10922v2, PDF p. 18, Lemma 7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P25

noncomputable section

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intakenext100.P25

open QAlgorithms.RealRegisters (Hilbert)

/-- Shirokov, arXiv:1810.10922v2, PDF p.18, Lemma 7, equation (46).
The unique slice is chosen before the energy and satisfies the norm bound for
every E>0. Equality is equality on D(sqrt(G)); the environment is arbitrary
separable, including finite dimensional spaces. -/
theorem lemma7_uniqueSlice {K : Type*} [Countable K]
    (G : EnergyObservable) (V : G.root.domain →ₗ[ℂ] Hilbert (ℕ × K))
    (hV : RelativelyBounded G V) (tau : Hilbert K) (htau : ‖tau‖ = 1) :
    ∃! W : G.root.domain →ₗ[ℂ] Hilbert ℕ,
      RelativelyBounded G W ∧
      (∀ E : ℝ, 0 < E → operatorEnergyNorm G W E ≤ operatorEnergyNorm G V E) ∧
      (∀ (x : G.root.domain) (psi : Hilbert ℕ),
        tensorBra psi tau (V x) = inner ℂ psi (W x)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P25

end
