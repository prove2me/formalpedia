-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_vacuumLocalMinimum
-- name    : QAlgorithms.Papers.Independent.Next46.P27.vacuumLocalMinimum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:28:33.483933+00:00
-- url     : https://prove2.me/theorems/9c4148a1-a78d-40a2-b2d0-0b263bb52aa3
-- title:
--   Finite-noise vacuum local minimum among pure inputs
-- statement:
--   For each noise variance $v>0$, let $\rho_0=|0\rangle\langle0|$ be the vacuum density on the full Fock space. It is a normalized pure state. There exists $r>0$ such that every unit vector $u$ with $\||u\rangle\langle u|-\rho_0\|_1<r$ satisfies
--
--   $$S(\Phi_v(\rho_0))\le S(\Phi_v(|u\rangle\langle u|)).$$
--
--   Entropies are in nats and may be infinite for unrestricted inputs. This is the local finite-thermalization endpoint obtained as the thermal input entropy approaches zero; it is not the global finite conjecture.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 4, Section VI and Appendix 2: finite-noise vacuum endpoint

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF pp.4–5, Section VI and Appendix 2: finite-noise vacuum endpoint is a
local minimum among normalized pure inputs. No global minimum is asserted. -/
theorem vacuumLocalMinimum (v : ℝ) (hv : 0 < v) :
    PureLocalOutputMinimum v (B.fockDyad 0 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
