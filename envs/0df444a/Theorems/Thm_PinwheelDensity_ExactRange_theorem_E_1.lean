-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_theorem_E_1
-- name    : PinwheelDensity.ExactRange.theorem_E_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:15.380298+00:00
-- url     : https://prove2.me/theorems/6c1a10a4-234c-47eb-9b2e-a64a943de4f1
-- title:
--   Theorem E.1 — certificate lifting, for all parameters and all data
-- statement:
--   For all parameters $(m,B,\theta_0)$ and all run data: if the run is accepted by the explicit checker, then every list of positive integers with all periods at least $m$ and density at most $B$ is schedulable.
--
--   The checker tests the parameters ($1\le m$, $\theta_0\ge4$ even, $0\le B\le1$), recomputes all case sets, generators and enumerations, and reads only witnesses from the data. No relation between $m$, $\theta_0$ and $B$ is assumed, and nothing is asserted about the existence of accepted runs. Soundness for arbitrary data is what makes the search behind Theorems 1.2 and 1.3 untrusted.
--
--   **Formalization Note** Kawamura's 5/6 theorem is not a hypothesis of this statement; proving it needs the Open platform theorem `pinwheel_conjecture`.
--
--   Differences from the source:
--   - encoding: acceptance by the Lean checker `PWGC.checkAllG`, whose text the paper cites → `checkRun`, written from the description in Appendices B–E, with a Lean data format of its own; reason: the source's Lean is not on the platform and targets another Lean and Mathlib revision; the tests are those the Appendices state
--   - encoding: instances are written as nondecreasing lists → a `List ℕ` in any order; reason: tasks are list positions, and density and schedulability do not depend on the order (Lemma A.2), so the same instances are covered
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Theorem E.1, p. 16 (PDF p. 16); also stated as Theorem 3.1, p. 8

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_cellOf
import Definitions.Def_PinwheelDensity_ExactRange_checkRun

namespace PinwheelDensity.ExactRange

/-- Theorem E.1 (Certificate lifting), p. 16: for all parameters and all data, acceptance of the run
by the explicit checker gives the guarantee `S(m, B)`. -/
theorem theorem_E_1 (P : Params) (d : Run) (h : checkRun P d = true) :
    Guarantee P.m P.B := by sorry

end PinwheelDensity.ExactRange
