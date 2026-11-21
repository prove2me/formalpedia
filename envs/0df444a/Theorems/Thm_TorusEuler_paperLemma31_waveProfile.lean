-- Prove2me | Theorems.Thm_TorusEuler_paperLemma31_waveProfile
-- name    : TorusEuler.paperLemma31_waveProfile
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T19:41:16.973429+00:00
-- url     : https://prove2.me/theorems/66ac82d7-ee32-4637-b0de-2df602be6c4f
-- title:
--   Lemma 3.1 — the localized odd periodic profile family
-- statement:
--   **Lemma 3.1 of the frozen manuscript (cc:uf:exact:lem:profile).** There exist two families of smooth functions $F_h,P_h:\mathbb{R}\to\mathbb{R}$, indexed by a scale $0<h\le1$, and a constant $C>0$ such that for every $0<h\le1$:
--
--   1. $F_h$ is $C^\infty$, **odd**, and $1$-periodic; $P_h$ is $C^\infty$, $1$-periodic, has **zero phase mean** $\int_0^1 P_h=0$, and is a primitive of $F_h$ ($P_h'=F_h$ everywhere);
--   2. $F_h'(0)=1$;
--   3. the slope and size bounds hold pointwise in the phase $s$:
--   $$-Ch\le F_h'(s)\le1,\qquad |F_h(s)|\le Ch;$$
--   4. for every integer $j\ge2$ there is a constant $C_j>0$, independent of $h$, with
--   $$|\partial_s^j F_h(s)|\le C_j\,h^{1-j}\qquad\text{for all }s.$$
--
--   The profile prescribes the central velocity gradient of each localized wave ($F_h'(0)=1$ gives gradient $a\otimes k$ at the origin) while keeping the wave itself small in velocity ($\|F_h\|_\infty\le Ch$) and its pressure Hessian controlled from below ($F_h'\ge-Ch$). The bounds are pointwise in phase, hence also bound the supremum over a period.
--
--   **Formalization Note** The uniform constant $C$ is chosen once for all scales; each $C_j$ is chosen after $j$ and before $h$. The exponent $h^{1-j}$ is an integer power (`zpow`) of the positive real $h$.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/PaperParameterAndLaunchStatements.lean#L38; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/04_localized_wave.tex#L152 (cc:uf:exact:lem:profile).

import Mathlib
import Definitions.Def_TorusEuler_Phase

open Filter Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

/-- `cc:uf:exact:lem:profile`. Bounds are pointwise in phase, so each also
bounds the supremum over a period. Uniform constants are chosen after the
two profile families and before the scale and phase. -/
theorem paperLemma31_waveProfile :
    ∃ (F P : ℝ → ℝ → ℝ) (C : ℝ), 0 < C ∧
      (∀ h, 0 < h → h ≤ 1 →
        ContDiff ℝ ∞ (F h) ∧ Function.Odd (F h) ∧ Function.Periodic (F h) 1 ∧
        ContDiff ℝ ∞ (P h) ∧ Function.Periodic (P h) 1 ∧ phaseMean (P h) = 0 ∧
        (∀ s, HasDerivAt (P h) (F h s) s) ∧ deriv (F h) 0 = 1 ∧
        ∀ s, -C * h ≤ deriv (F h) s ∧ deriv (F h) s ≤ 1 ∧ ‖F h s‖ ≤ C * h) ∧
      ∀ j : ℕ, 2 ≤ j → ∃ Cj : ℝ, 0 < Cj ∧ ∀ h, 0 < h → h ≤ 1 → ∀ s,
        ‖iteratedDeriv j (F h) s‖ ≤ Cj * h ^ (1 - (j : ℤ)) := by sorry

end TorusEuler
