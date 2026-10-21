-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_lemma_3_9
-- name    : SwitchOptStop.Boundary.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:56.992841+00:00
-- url     : https://prove2.me/theorems/a2e0273d-e5fe-4b8b-979c-517cd9e7a567
-- title:
--   Lemma 3.9, p. 12 — V(ι, ·) ∈ C²(C_ι) and 𝕃V − λV = −H on C (3.11)
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. For each regime $\iota$, $V(\iota,\cdot)$ is twice continuously differentiable on $C_\iota$, and $V$ solves in the classical sense
--   $$
--   \mathbb LV(\iota,x)-\lambda(\iota)V(\iota,x)=-H(\iota,x)\qquad\text{for }(\iota,x)\in C, \tag{3.11}
--   $$
--   with $\mathbb L$ the generator (2.4) of $(\alpha,X)$.
--
--   Interior regularity is the first half of the free-boundary characterization of $V$.
--
--   **Formalization Note** $C_\iota$ is open (Lemma 3.5 gives continuity of $V$), so `ContDiffOn ℝ 2` on it is classical $C^2$ and the derivatives in $\mathbb L$ are the Fréchet derivatives.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 12, Lemma 3.9, (3.11)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Lemma 3.9 (p. 12): `V(ι, ·) ∈ C²(C_ι)` and `𝕃V − λV = −H` on `C` (3.11). -/
theorem lemma_3_9 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    ∀ ι : Fin 2,
      ContDiffOn ℝ 2 (value m S ι) (contSet m S ι) ∧
      ∀ x ∈ contSet m S ι, gen m (value m S) ι x - m.lam ι * value m S ι x = -m.H ι x := by sorry

end SwitchOptStop.Boundary
