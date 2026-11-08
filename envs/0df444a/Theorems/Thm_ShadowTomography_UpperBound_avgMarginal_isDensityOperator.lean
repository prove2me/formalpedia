-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_avgMarginal_isDensityOperator
-- name    : ShadowTomography.UpperBound.avgMarginal_isDensityOperator
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:20.012136+00:00
-- url     : https://prove2.me/theorems/9c7e379d-894f-4999-b44e-320faac8a3c6
-- title:
--   The average one-register marginal of a state is a state
-- statement:
--   Let $\sigma$ be a density operator on $q\ge 1$ registers, $\sigma\in\mathcal D(\mathcal H^{\otimes q})$. For each register $r$ let $\sigma_r=\operatorname{Tr}_{-r}\sigma$ be its reduced state (all other $q-1$ registers traced out), and let
--   $$
--   \bar\sigma=\frac1q\sum_{r=1}^{q}\sigma_r
--   $$
--   be the average one-register marginal. Then $\bar\sigma$ is a density operator on $\mathcal H$.
--
--   In Aaronson's shadow-tomography algorithm the hypothesis state lives on $q$ registers and its estimates $x_i=\operatorname{Tr}(E_i\bar\sigma)$ are read off the average marginal; this lemma guarantees these are genuine acceptance probabilities in $[0,1]$.
--
--   **Formalization Note** The hypothesis $q\ge1$ is needed: for $q=0$ the definition `avgMarginal` returns $0$.
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

/-- **K5b.** The average one-register marginal of a density operator on `q ≥ 1` registers is a
density operator. -/
theorem avgMarginal_isDensityOperator {n : Type} [Fintype n] [DecidableEq n] {q : ℕ}
    (hq : 1 ≤ q) (σ : Matrix (Fin q → n) (Fin q → n) ℂ) (hσ : WildeQIT.IsDensityOperator σ) :
    WildeQIT.IsDensityOperator (avgMarginal σ) := by
  sorry

end ShadowTomography.UpperBound
