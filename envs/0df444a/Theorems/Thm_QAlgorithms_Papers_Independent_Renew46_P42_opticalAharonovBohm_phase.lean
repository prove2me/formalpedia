-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_opticalAharonovBohm_phase
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.opticalAharonovBohm_phase
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:29:30.62299+00:00
-- url     : https://prove2.me/theorems/fc7e6099-3c18-4097-a127-6a2e62877fbf
-- title:
--   Optical Aharonov–Bohm loop phase
-- statement:
--   In the stipulated stationary first-order magnetic optical model let $c,W,\omega,r>0$ and constant $n\ge1$. The excluded-core vortex is $\mathbf u=(W/r)\mathbf e_\phi$ with positive circulation. The circulation phase of $\mathbf A=(n^2-1)\omega\mathbf u/c^2$ around one positive circular circuit is
--
--   $$\varphi_{\mathrm{AB}}=\oint\mathbf A\cdot d\mathbf x=2\pi\frac\omega c(n^2-1)\frac Wc.$$
--
--   In Cartesian coordinates $\nabla\times\mathbf u=0$ wherever $x^2+y^2>0$. Integrating around $N$ positive circuits, for any natural number $N$, multiplies the phase by $N$.
--
--   This describes the loop phase in the retained magnetic model rather than an exact finite-flow Maxwell solution; the frequency occurs to the first power.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 7, §IV A, (62)–(64): optical Aharonov–Bohm phase

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.7, (62)–(64): one positive circuit in the stipulated first-order
magnetic optical model gives the optical Aharonov–Bohm phase. -/
theorem opticalAharonovBohm_phase (c n omega W r : ℝ)
    (hc : 0 < c) (hn : 1 ≤ n) (ho : 0 < omega) (hW : 0 < W) (hr : 0 < r) :
    vortexPhase c n omega W r = 2 * Real.pi * (omega / c) * (n ^ 2 - 1) * (W / c) ∧
    (∀ x : V3, 0 < x 0 ^ 2 + x 1 ^ 2 →
      curl3 (fun y => (W / (y 0 ^ 2 + y 1 ^ 2)) • ![-y 1, y 0, 0]) x = 0) ∧
    (∀ turns : ℕ,
      ((n ^ 2 - 1) * omega / c ^ 2) *
        (∫ phi in (0 : ℝ)..((turns : ℝ) * (2 * Real.pi)),
          dot3 (slowVortexPolar W r phi) (r • azimuth phi)) =
        (turns : ℝ) * vortexPhase c n omega W r) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
