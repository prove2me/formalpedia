-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_amp_isEffect
-- name    : ShadowTomography.UpperBound.amp_isEffect
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:20.339422+00:00
-- url     : https://prove2.me/theorems/37c2dea8-d42a-4877-a69f-07ed75ba23d3
-- title:
--   Amplified count measurements are effects
-- statement:
--   Let $E$ be a two-outcome measurement (an effect, $0\preceq E\preceq I$) on $\mathcal H$, let $q\ge0$ and $\theta\in\mathbb R$. Apply $E$ to each of $q$ registers and count the number $S$ of accepting invocations. The measurements on $\mathcal H^{\otimes q}$ that accept iff $S\ge\theta q$, respectively iff $S\le\theta q$, namely
--   $$
--   E^{\ge\theta}_q=\sum_{T\subseteq[q],\ |T|\ge\theta q}\ \bigotimes_{r\in T}E\otimes\bigotimes_{r\notin T}(I-E),\qquad
--   E^{\le\theta}_q=\sum_{T\subseteq[q],\ |T|\le\theta q}\ \bigotimes_{r\in T}E\otimes\bigotimes_{r\notin T}(I-E),
--   $$
--   are again effects: $0\preceq E^{\ge\theta}_q\preceq I$ and $0\preceq E^{\le\theta}_q\preceq I$.
--
--   These amplified measurements are the tests $E^*_{i,t,\pm}$ and update measurements $F_t$ of the shadow-tomography algorithm (p. 16); being effects is what allows Gentle Search, the quantum union bound and Lüders post-selection to be applied to them.
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

/-- **K5c.** The amplified count measurements built from an effect are effects. -/
theorem amp_isEffect {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n ℂ)
    (hE : IsEffect E) (q : ℕ) (θ : ℝ) :
    IsEffect (ampAtLeast E q θ) ∧ IsEffect (ampAtMost E q θ) := by
  sorry

end ShadowTomography.UpperBound
