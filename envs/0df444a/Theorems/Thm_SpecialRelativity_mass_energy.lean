-- Prove2me | Theorems.Thm_SpecialRelativity_mass_energy
-- name    : SpecialRelativity.mass_energy
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T01:50:08.279435+00:00
-- url     : https://prove2.me/theorems/3708a7d0-9a6d-5d01-a788-c87b6ba82840
-- title:
--   Mass-energy equivalence: the energy-momentum relation (goal)
-- statement:
--   **Mass–energy equivalence — the energy–momentum relation, the goal theorem.**
--
--   The source: "Combined with other laws of physics, the two postulates of special relativity predict the equivalence of mass and energy, as expressed in the mass–energy equivalence formula E=mc2"; and "The energy and momentum, which are separate in Newtonian mechanics, form a four-vector in relativity, and this relates the time component (the energy) to the space components (the momentum) in a non-trivial way."
--
--   Let `m` be a rest mass with $m \ge 0$, and let a particle move with velocity `v` in coordinate-time parametrization ($v_0 = 1$, spatial speed $s < 1$), with four-momentum
--
--   $$P = m\,\gamma\,(1, v_1, v_2, v_3), \qquad \gamma = 1/\sqrt{1 - s^2}$$
--
--   (time component the energy $E = m\gamma$, spatial components the momentum $p = m\gamma\,v$, in units $c = 1$).
--
--   **Conclusion:** the four-momentum has invariant norm that of the rest mass:
--
--   $$\eta(P, P) \;=\; -\,m^2.$$
--
--   Unwrapping $\eta$ this is the energy–momentum relation
--
--   $$E^2 - |p|^2 = m^2 \qquad (\text{i.e. } E^2 = |p|^2 + m^2c^2 \text{ in general units}),$$
--
--   the invariant content of mass–energy equivalence: at zero velocity it reads $E = m$ (the rest energy $E = mc^2$ in units $c = 1$), and for light ($m = 0$) it reads $E = |p|$.
--
--   **Formalization note.** Computation only: $\eta(P, P) = m^2\gamma^2\,(-1 + v_1^2 + v_2^2 + v_3^2) = m^2\gamma^2\,(-1 + s^2) = -m^2$, the last step by $\gamma^2 = 1/(1 - s^2)$. The dynamical derivation of $E = mc^2$ from conservation laws (Einstein 1905) is out of scope and disclosed in the mission description; the theorem asserts the kinematic invariant relation, which is what "E=mc2" rigorously means in this framework.
-- source:
--   Wikipedia, Special relativity, https://en.wikipedia.org/wiki/Special_relativity (source of the quoted statements, reproduced verbatim in the definition file) (Mass-energy equivalence: 'E=mc2'; 'The energy and momentum ... form a four-vector in relativity'); A. Einstein, Ist die Traegheit eines Koerpers von seinem Energieinhalt abhaengig?, Annalen der Physik 18 (1905), 639-641; H. Minkowski (1908)

import Mathlib
import Definitions.Def_SpecialRelativity

namespace SpecialRelativity

/-- The goal — mass–energy equivalence in its precise form, the energy–momentum
relation.  The source: "Combined with other laws of physics, the two postulates
of special relativity predict the equivalence of mass and energy, as expressed
in the mass–energy equivalence formula E=mc2"; "The energy and momentum, which
are separate in Newtonian mechanics, form a four-vector in relativity, and this
relates the time component (the energy) to the space components (the momentum)
in a non-trivial way."

For a particle of rest mass `m ≥ 0` moving with velocity `v` (coordinate-time
parametrization `v 0 = 1`, spatial speed `s < 1`), the four-momentum is
`P = m γ (1, v₁, v₂, v₃)` with `γ = 1/√(1-s²)`: time component the energy
`E = m γ`, spatial components the momentum `p = m γ v` (units `c = 1`).  The
assertion `η(P, P) = -m²` is the energy–momentum relation

`E² - |p|² = m²`  (i.e.  `E² = |p|² + m²c²` in general units),

the invariant content of mass–energy equivalence: at zero velocity it reads
`E = m`, and for light (`m = 0`) it reads `E = |p|`. -/
theorem mass_energy (m : ℝ) (hm : 0 ≤ m) (v : Sp) (hv0 : v 0 = 1)
    (hsp : spatialSpeed v < 1) :
    mink (fourMomentum m v) (fourMomentum m v) = -(m * m) := by
  sorry

end SpecialRelativity
