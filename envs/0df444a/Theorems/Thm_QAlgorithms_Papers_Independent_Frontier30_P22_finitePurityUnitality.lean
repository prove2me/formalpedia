-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P22_finitePurityUnitality
-- name    : QAlgorithms.Papers.Independent.Frontier30.P22.finitePurityUnitality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:21:51.438008+00:00
-- url     : https://prove2.me/theorems/8e40af4f-3fc9-4927-aeb2-aafa8a190871
-- title:
--   Finite-dimensional purity decrease is equivalent to unitality
-- statement:
--   Let $d\ge1$, let $H$ be a Hermitian $d\times d$ matrix, and let $(F_\alpha)$ be any finite family of complex $d\times d$ matrices, including the empty family. Set
--   $$
--   \mathcal L(X)=\sum_\alpha\left(F_\alpha X F_\alpha^\dagger-\frac12\{F_\alpha^\dagger F_\alpha,X\}\right),\qquad G(X)=-i[H,X]+\mathcal L(X),\qquad\Phi_t=e^{tG}.
--   $$
--   Here $[A,B]=AB-BA$, $\{A,B\}=AB+BA$, and a density matrix is positive semidefinite with trace one. For every density matrix $\rho$, purity $p(\rho)=\operatorname{Tr}(\rho^2)$ is nonincreasing along $\Phi_t$, for $t\ge0$, if and only if
--   $$
--   \mathcal L(I)=G(I)=\sum_\alpha[F_\alpha,F_\alpha^\dagger]=0.
--   $$
--   Equivalently, $2\operatorname{Re}\operatorname{Tr}(\rho G(\rho))\le0$ for every density matrix if and only if the same identity image vanishes.
--
--   This gives the finite-dimensional necessity-and-sufficiency interface, including $d=1$ and Hamiltonian-only dynamics.
-- source:
--   Conditions for strictly purity-decreasing quantum Markovian dynamics, arXiv:quant-ph/0411119v2, PDF p. 2, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P22

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P22

local notation "FD" => QAlgorithms.Papers.Independent.Dependency50.P16.LindbladData

local notation "finiteG" => QAlgorithms.Papers.Independent.Dependency50.P16.gkslGenerator

local notation "finiteEvolution" => QAlgorithms.Papers.Independent.Dependency50.P16.semigroupEvolution

/-- Theorem 2, PDF p.2, proved on p.3: for every nonzero finite dimension,
purity is nonincreasing for every density iff the dissipator annihilates I.
The equivalent instantaneous condition uses the source-normalized factor 2.
The accepted GKSL data use G=-i[H,.]+L with a one-half anticommutator. -/
theorem finitePurityUnitality {d : ℕ} (hd : 1 ≤ d) (D : FD d) :
    (finitePurityNonincreasing D ↔ finiteIdentityImage D = 0) ∧
    ((∀ rho : Matrix (Fin d) (Fin d) ℂ, QAlgorithms.IsDensityMatrix rho →
      2 * (rho * finiteG D rho).trace.re ≤ 0) ↔ finiteIdentityImage D = 0) ∧
    finiteG D 1 = finiteIdentityImage D := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P22

end
