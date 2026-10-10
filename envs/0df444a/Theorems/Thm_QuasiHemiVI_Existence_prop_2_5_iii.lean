-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_prop_2_5_iii
-- name    : QuasiHemiVI.Existence.prop_2_5_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:33:58.444186+00:00
-- url     : https://prove2.me/theorems/041df9d8-e0a5-4cf6-8ba7-110b36e804f4
-- title:
--   Proposition 2.5 (iii) — $(u,v)\mapsto J^0(u;v)$ is upper semicontinuous
-- statement:
--   Let $X$ be a real Banach space and $J:X\to\mathbb R$ locally Lipschitz. Then the function
--
--   $$
--   X\times X\ni(u,v)\longmapsto J^0(u;v)\in\mathbb R
--   $$
--
--   is upper semicontinuous (for the norm topology of $X\times X$).
--
--   This is what allows passing to the upper limit in the term $J^0(\gamma v_t;\gamma(w-u))$ in the proofs of Theorem 3.4 (i) and Theorem 3.8 (ii).
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1249, Proposition 2.5 (iii)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv

namespace QuasiHemiVI.Existence

/-- Proposition 2.5 (iii), p. 1249: for a locally Lipschitz `J` on a Banach space `X`, the map
`X × X ∋ (u, v) ↦ J⁰(u; v)` is upper semicontinuous. -/
theorem prop_2_5_iii {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (J : X → ℝ) (hJ : LocallyLipschitz J) :
    UpperSemicontinuous (fun p : X × X => clarkeDeriv J p.1 p.2) := by sorry

end QuasiHemiVI.Existence
