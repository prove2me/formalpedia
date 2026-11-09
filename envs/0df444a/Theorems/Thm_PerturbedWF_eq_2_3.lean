-- Prove2me | Theorems.Thm_PerturbedWF_eq_2_3
-- name    : PerturbedWF.eq_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:41:54.078204+00:00
-- url     : https://prove2.me/theorems/dbd69f70-c8c7-4b16-b27d-a8ea3d7ac435
-- title:
--   Eq. (2.3): $\langle v,x-y\rangle\le\|x-y\|$ for $v\in B^*$ and $x,y\in\mathcal C$
-- statement:
--   Let $\mathcal C$ be a configuration space over a finite metric $d$ with transportation norm $\|\cdot\|$. For every $v\in B^*$, i.e. $|v_i-v_j|\le d(i,j)$ for all $i,j$,
--   $$\langle v,x-y\rangle\le\|x-y\|\qquad\forall x,y\in\mathcal C.\qquad(2.3)$$
--
--   This duality inequality is used throughout the analysis (Lemmas 2.3 and 3.1).
--
--   **Formalization Note.** $B^*$ is `dualBall d` and $\|\cdot\|$ is `transNorm d`, defined by (2.1).
--
--   Differences from the source:
--   - encoding: v ∈ B* = {v : ‖v‖* ≤ 1} → v ∈ dualBall d, i.e. |v_i − v_j| ≤ d(i, j) for all i, j; reason: the characterization of B* stated after (2.2), p.5 (v ∈ B* iff |v_i − v_j| ≤ d(i, j)); the same set
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), eq. (2.3), p.5 (PDF p.6)

import Mathlib
import Definitions.Def_PerturbedWF_WClass

namespace PerturbedWF

/-- **Eq. (2.3)** (p.5, PDF p.6). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

For `v ∈ B*`, `⟨v, x − y⟩ ≤ ‖x − y‖` for all `x, y ∈ C`.

**Formalization Note.** `B*` is `dualBall d` (`|v_i − v_j| ≤ d(i, j)`), `‖·‖` the
transportation norm (2.1). -/
theorem eq_2_3 {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (hC : IsConfigSpace C) (d : ι → ι → ℝ) (hd : IsFinMetric d) (v : ι → ℝ)
    (hv : v ∈ dualBall d) (x y : ι → ℝ) (hx : x ∈ C) (hy : y ∈ C) :
    dot v (x - y) ≤ transNorm d (x - y) := by sorry

end PerturbedWF
