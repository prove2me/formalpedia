-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P50_minimal_backward_existence
-- name    : QAlgorithms.Papers.Independent.Claimed50.P50.minimal_backward_existence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:17:39.725301+00:00
-- url     : https://prove2.me/theorems/a20d6bfd-746e-499b-a1fc-9bfa71145ce2
-- title:
--   Minimal backward dynamical-semigroup solution
-- statement:
--   Let $H$ and $H_0$ be complex Hilbert spaces, $D$ a dense complex linear subspace of $H$, and $L:D\to H\otimes H_0$ and $K:D\to H$ linear operators. The tensor product is completed. Suppose $K$ is closable with maximal accretive closure, and $\|L\psi\|^2\le 2\operatorname{Re}\langle\psi,K\psi\rangle$ for every $\psi\in D$. Define
--
--   $$\ell(\psi,X,\phi)=\langle L\psi,(X\otimes I)L\phi\rangle-\langle K\psi,X\phi\rangle-\langle\psi,XK\phi\rangle.$$
--
--   There exists a normal, subunital, completely positive dynamical semigroup $\Phi^\infty$ on the entire bounded-operator algebra, starting at the identity and having weak-star continuous orbits, such that, for all $X\in\mathcal B(H)$, $\psi,\phi\in D$ and $t\ge0$,
--
--   $$\frac{d}{dt}\langle\psi,\Phi^\infty_t(X)\phi\rangle=\ell(\psi,\Phi^\infty_t(X),\phi).$$
--
--   The derivative at zero is a right derivative. For every other such dynamical-semigroup solution $\Phi$, the map $\Phi_t-\Phi^\infty_t$ is completely positive at every nonnegative time. This gives existence and minimality without asserting that the rank-one test span is a generator core.
--
--   **Formalization Note** Normality is expressed through weak-operator continuity on the operator-norm unit ball; on that ball the source identifies this topology with weak-star topology. No independent purported preadjoint generator is introduced.
-- source:
--   Covariant Quantum Dynamical Semigroups: Unbounded generators, arXiv:quant-ph/9701037v1, PDF p. 4, §2: existence and CP-order minimality of the backward solution

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P50

open scoped TensorProduct BigOperators

variable {H N : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

/-- Holevo, arXiv:quant-ph/9701037v1, PDF pp.4–5: existence of a minimal
normal subunital completely positive dynamical-semigroup solution of (9).
The operators are given before the solution; graph-core density is not assumed
or asserted. The trace-class preadjoint is not substituted by a free generator. -/
theorem minimal_backward_existence {D : Submodule ℂ H}
    (hDense : Dense (D : Set H)) (S : StandardData (N := N) D)
    (hDiss : IsDissipative S) (hK : HasMaximalAccretiveClosure S) :
    ∃ Phi : DynamicalSemigroup H, IsMinimalBackward S Phi := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P50

end
