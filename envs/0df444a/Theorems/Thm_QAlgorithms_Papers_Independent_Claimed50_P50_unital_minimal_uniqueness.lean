-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P50_unital_minimal_uniqueness
-- name    : QAlgorithms.Papers.Independent.Claimed50.P50.unital_minimal_uniqueness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:18:23.510287+00:00
-- url     : https://prove2.me/theorems/c88edf77-1b45-4b0c-9099-e3a4d05585f1
-- title:
--   Unital minimal backward solutions are unique
-- statement:
--   Let $H,H_0$ be complex Hilbert spaces, $D\subset H$ a dense complex linear subspace, and $L:D\to H\otimes H_0$, $K:D\to H$ linear operators. Suppose $K$ is closable with maximal accretive closure and the form is conservative:
--
--   $$\|L\psi\|^2=2\operatorname{Re}\langle\psi,K\psi\rangle\qquad(\psi\in D).$$
--
--   Use the standard form $\ell(\psi,X,\phi)=\langle L\psi,(X\otimes I)L\phi\rangle-\langle K\psi,X\phi\rangle-\langle\psi,XK\phi\rangle$. Let $\Phi^\infty$ be a minimal normal subunital completely positive dynamical-semigroup solution of the backward equation with identity initial condition, where minimality means complete-positive domination by every competing solution at each time. If $\Phi^\infty_t(I)=I$ for every $t\ge0$, then every normal subunital completely positive dynamical-semigroup solution $\Psi$ of that same equation satisfies
--
--   $$\Psi_t(X)=\Phi^\infty_t(X)\qquad(t\ge0,\ X\in\mathcal B(H)).$$
--
--   This distinguishes conservativity of the form from actual unitality of its minimal evolution. All semigroups have weak-star continuous orbits, and the derivative at zero is taken from the right.
-- source:
--   Covariant Quantum Dynamical Semigroups: Unbounded generators, arXiv:quant-ph/9701037v1, PDF p. 4, §2: a unital minimal backward solution is unique

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P50

open scoped TensorProduct BigOperators

variable {H N : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

/-- Holevo, arXiv:quant-ph/9701037v1, PDF p.4, final sentence of Section 2
on that page: a unital minimal backward solution is the unique solution.
Conservativity of the form and unitality of the semigroup are separate
hypotheses; competitors may be subunital. -/
theorem unital_minimal_uniqueness {D : Submodule ℂ H}
    (hDense : Dense (D : Set H)) (S : StandardData (N := N) D)
    (hConservative : IsConservativeForm S)
    (hK : HasMaximalAccretiveClosure S) (Phi : DynamicalSemigroup H)
    (hMinimal : IsMinimalBackward S Phi) (hUnital : IsUnitalQDS Phi) :
    ∀ Psi : DynamicalSemigroup H, SolvesBackward S Psi →
      ∀ (t : NNReal) (X : H →L[ℂ] H), Psi.maps t X = Phi.maps t X := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P50

end
