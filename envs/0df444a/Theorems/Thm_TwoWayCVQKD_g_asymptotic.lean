-- Prove2me | Theorems.Thm_TwoWayCVQKD_g_asymptotic
-- name    : TwoWayCVQKD.g_asymptotic
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T06:44:09.896938+00:00
-- url     : https://prove2.me/theorems/cde0ebfb-e696-44a9-93d4-71da9dd0a9e9
-- title:
--   Eq. (3): $g(\nu)=\log(e\nu/2)+O(\nu^{-1})$
-- statement:
--   Let $g(\nu)=\frac{\nu+1}{2}\log\frac{\nu+1}{2}-\frac{\nu-1}{2}\log\frac{\nu-1}{2}$ be the entropy function of Eq. (3). Then, for $\nu\gg1$,
--   $$
--   g(\nu)=\log\frac{e\nu}{2}+O(\nu^{-1}).
--   $$
--   This asymptotic form is what turns the entropies of the large symplectic eigenvalues into the logarithms of the closed-form rates, and it is the source of the number $e$ in Eqs. (34), (46), (73) and (83).
--
--   Differences from the source:
--   - encoding: log in bits or nats → natural logarithm; reason: the paper allows either unit (p.6), and a rate in bits is the rate in nats divided by ln 2
--   - encoding: O(ν⁻¹) for ν ≫ 1 → =O[atTop] in ν; reason: the usual meaning of the paper's asymptotic notation
-- source:
--   Pirandola, Mancini, Lloyd, Braunstein, Continuous Variable Quantum Cryptography using Two-Way Quantum Communication, arXiv:quant-ph/0611167v3, Eq. (3), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)
open Asymptotics Filter

namespace TwoWayCVQKD

/-- Pirandola, Mancini, Lloyd, Braunstein, arXiv:quant-ph/0611167v3, Eq. (3), p.6:
`g(ν) → log(eν/2) + O(ν⁻¹)` for `ν ≫ 1`.

**Formalization Note** `symplecticEntropy` is `g`, with natural logarithms. -/
theorem g_asymptotic :
    (fun ν : ℝ => symplecticEntropy ν - Real.log (Real.exp 1 * ν / 2)) =O[atTop]
      (fun ν : ℝ => ν⁻¹) := by sorry

end TwoWayCVQKD
