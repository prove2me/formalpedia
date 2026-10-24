-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P01_pureStatePreserving_classification
-- name    : QAlgorithms.Papers.Independent.Support50.P01.pureStatePreserving_classification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:19:24.083283+00:00
-- url     : https://prove2.me/theorems/9246374c-883c-4971-88d8-fe08989ebf4a
-- title:
--   Theorem 2: classification of pure-state-preserving channels
-- statement:
--   Let $A=\mathbb C^a$, $B=\mathbb C^b$, and $E=\mathbb C^e$ have positive finite dimensions and fixed orthonormal bases. Fix an isometry $U:A\to B\otimes E$ and define the channel $\mathcal N(X)=\operatorname{Tr}_E(UXU^\dagger)$ and its genuine complement $\mathcal N^c(X)=\operatorname{Tr}_B(UXU^\dagger)$. Density operators are positive semidefinite with trace one, and all entropies use base-two logarithms with $0\log 0=0$. Write $I_c(\mathcal N,\rho)=H(\mathcal N(\rho))-H(\mathcal N^c(\rho))$, $Q^{(1)}(\mathcal N)=\sup_\rho I_c(\mathcal N,\rho)$, and $Q(\mathcal N)=\sup_{n\ge1}Q^{(1)}(\mathcal N^{\otimes n})/n$, with arbitrary entangled block inputs. Conjugate degradability means one CPTP map $D$ satisfies $D\mathcal N(X)=(\mathcal N^c(X))^T$ for every operator $X$; conjugate antidegradability reverses the receiver and environment in this identity. Suppose every unit vector $\psi\in A$ has output $\mathcal N(|\psi\rangle\langle\psi|)$ equal to the projector onto some unit vector of $B$. Then at least one of the following alternatives holds:
--   $$
--   \begin{aligned}
--   & a\le b,\quad \mathcal N(X)=VXV^\dagger\ (\text{all }X),\quad V^\dagger V=I_A,\quad
--   \operatorname{rank}J(\mathcal N)=1,\quad\mathcal N\text{ conjugate degradable};\\
--   & \mathcal N(X)=\operatorname{Tr}(X)|\phi\rangle\langle\phi|\ (\text{all }X),\quad
--   \|\phi\|=1,\quad\mathcal N\text{ conjugate antidegradable}.
--   \end{aligned}
--   $$
--   Here $J$ is the unnormalized Choi matrix. The alternatives need not be exclusive when the input dimension is one.
-- source:
--   Conjugate Degradability and the Quantum Capacity of Cloning Channels, arXiv:0909.3297v1, PDF p. 12, Theorem 2: classification of pure-state-preserving channels

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P01

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (receiverChannel complementaryChannel IsDegradable dilationPower maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation quantumCapacity)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

open QAlgorithms.Papers.Independent.Dependency50.P41 (EntanglementBreaking)

open QAlgorithms.Papers.Independent.Dependency50.P40 (outputFirstChoi)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {a b e c : ℕ}

/-- PDF p.12, Theorem 2: exhaustive, nonexclusive classification of pure-state-preserving channels. -/
theorem pureStatePreserving_classification (ha : 0<a) (hb : 0<b) (he : 0<e)
    (U : Matrix (Fin b × Fin e) (Fin a) ℂ) (hU : Uᴴ * U = 1)
    (hpure : ∀ psi : EuclideanSpace ℂ (Fin a), ‖psi‖ = 1 →
      ∃ phi : EuclideanSpace ℂ (Fin b), ‖phi‖ = 1 ∧
        receiverChannel U (pureDensity psi) = pureDensity phi) :
    (a≤b ∧ (∃ V : Matrix (Fin b) (Fin a) ℂ, Vᴴ * V = 1 ∧
      ∀ X, receiverChannel U X = V * X * Vᴴ) ∧
      (outputFirstChoi (receiverChannel U)).rank = 1 ∧ ConjugateDegradable U) ∨
    (∃ phi : EuclideanSpace ℂ (Fin b), ‖phi‖ = 1 ∧
      (∀ X, receiverChannel U X = X.trace • pureDensity phi) ∧ ConjugateAntidegradable U) := by sorry

end QAlgorithms.Papers.Independent.Support50.P01

end
