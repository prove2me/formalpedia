-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_tensorPow_isDensityOperator_le_one
-- name    : ShadowTomography.UpperBound.tensorPow_isDensityOperator_le_one
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:13.35213+00:00
-- url     : https://prove2.me/theorems/56df2c44-05f3-49e0-b66d-196bcc62fd7e
-- title:
--   Tensor powers of a density operator are density operators below the identity
-- statement:
--   Let $\rho$ be a density operator (positive semidefinite, trace one) on a finite-dimensional Hilbert space $\mathcal H$, and let $k\ge 0$. Then the $k$-fold tensor power $\rho^{\otimes k}$, acting on $\mathcal H^{\otimes k}$, is again a density operator, and it lies below the identity in the Loewner order:
--   $$
--   \rho^{\otimes k}\in\mathcal D(\mathcal H^{\otimes k}),\qquad \rho^{\otimes k}\preceq I .
--   $$
--   For $k=0$, $\rho^{\otimes 0}$ is the $1\times 1$ identity.
--
--   This is the basic bookkeeping fact behind every argument that measures many i.i.d. copies of an unknown state; the bound $\rho^{\otimes k}\preceq I$ yields the comparison $I/D^k\succeq D^{-k}\rho^{\otimes k}$ used in the potential argument of the shadow-tomography proof.
--
--   **Formalization Note** Operators on $\mathcal H^{\otimes k}$ are matrices indexed by $k$-tuples of basis labels (`tensorPow`); $\rho^{\otimes k}\preceq I$ is stated as positive semidefiniteness of $I-\rho^{\otimes k}$.
-- source:
--   S. Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, https://arxiv.org/abs/1711.01053, Section 5 (proof of Theorem 2), pp. 15-19

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
set_option autoImplicit false

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound

/-- **K5a.** A tensor power `ρ^{⊗k}` of a density operator is a density operator and lies
below the identity in the Loewner order (`ρ^{⊗k} ≤ 1`). -/
theorem tensorPow_isDensityOperator_le_one {n : Type} [Fintype n] [DecidableEq n]
    (ρ : Matrix n n ℂ) (hρ : WildeQIT.IsDensityOperator ρ) (k : ℕ) :
    WildeQIT.IsDensityOperator (tensorPow ρ k) ∧ (1 - tensorPow ρ k).PosSemidef := by
  sorry

end ShadowTomography.UpperBound
