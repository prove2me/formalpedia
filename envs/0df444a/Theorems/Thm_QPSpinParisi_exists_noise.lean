-- Prove2me | Theorems.Thm_QPSpinParisi_exists_noise
-- name    : QPSpinParisi.exists_noise
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:03:55.031774+00:00
-- url     : https://prove2.me/theorems/e212b233-25b6-4b30-a5ab-a9e760e9deae
-- title:
--   Section 2.1 — the Brownian noise and its integrals $\int\sqrt\zeta\,dB$ exist
-- statement:
--   Let $(c_p)_{p\ge2}$ satisfy the mixture assumption. There is a probability space carrying a standard Brownian motion $(B_t)_{0\le t\le1}$ in $\mathbb R^3$ together with the Wiener integrals
--   $$N^a_t=\int_0^t\sqrt{\zeta(r)}\,dB^a_r,\qquad a=1,2,3.$$
--   This is the standing setup of the control problem (2.3), and it shows that statements quantifying over all such noises are not vacuous.
--
--   Differences from the source:
--   - reading: "Let $(B_t)$ be a standard Brownian motion" and the integral $\int\sqrt\zeta\,dB$ → their existence is the statement; reason: the source presupposes it, and the statements of the mission quantify over all such objects
--   - encoding: $\int_s^1\sqrt{\zeta}\,dB$ → the increment of the process `noise` between $s$ and $1$; reason: the Wiener integral, tied to $B$ by `HasBrownianItoIntegral`
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, standing setup, p.4 (PDF p.4)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_BrownianNoise

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), §2.1, p.4, PDF p.4, standing setup ("Let `(B_t)_{0≤t≤1}` be a standard Brownian motion in `ℝ³`"): the noise of the control
problem (2.3) exists, with its Wiener integrals. Every statement quantifying over `W` is non-vacuous by this item. -/
theorem exists_noise (c : ℕ → ℝ) (hc : MixHyp c) : Nonempty (BrownianNoise c) := by sorry

end QPSpinParisi
