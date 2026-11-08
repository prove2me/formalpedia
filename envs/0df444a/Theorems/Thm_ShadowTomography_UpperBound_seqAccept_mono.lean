-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_seqAccept_mono
-- name    : ShadowTomography.UpperBound.seqAccept_mono
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:23.509708+00:00
-- url     : https://prove2.me/theorems/104d7bde-6efe-4c05-917a-eb8cd0fb97e1
-- title:
--   Sequential Lüders acceptance is monotone in the state
-- statement:
--   Let $F_0,\dots,F_{M-1}$ be operators on $\mathcal H$ and write $A=\sqrt{F_{M-1}}\cdots\sqrt{F_0}$, so that the probability that the measurements $F_0,\dots,F_{M-1}$, applied in succession by their Lüders instruments, all accept on $\sigma$ is
--   $$
--   \operatorname{acc}(F;\sigma)=\operatorname{Re}\operatorname{Tr}\big(A\sigma A^\dagger\big).
--   $$
--   If $\sigma,\rho$ are matrices and $c\in\mathbb R$ satisfy $\sigma\succeq c\,\rho$ (i.e. $\sigma-c\rho$ is positive semidefinite), then
--   $$
--   c\cdot \operatorname{acc}(F;\rho)\le \operatorname{acc}(F;\sigma).
--   $$
--
--   In the shadow-tomography proof this is applied with $\sigma=I/D^q$ and $\rho=\rho^{\otimes q}$ to transfer the quantum-union-bound lower bound from the true state to the maximally mixed starting hypothesis (p. 17).
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

/-- **K4a.** Sequential Lüders acceptance is monotone in the state: if `σ ⪰ c ρ` then
`seqAccept F σ ≥ c · seqAccept F ρ`. -/
theorem seqAccept_mono {n : Type} [Fintype n] [DecidableEq n] {M : ℕ}
    (F : Fin M → Matrix n n ℂ) (σ ρ : Matrix n n ℂ) (c : ℝ)
    (h : (σ - (c : ℂ) • ρ).PosSemidef) :
    c * seqAccept F ρ ≤ seqAccept F σ := by
  sorry

end ShadowTomography.UpperBound
