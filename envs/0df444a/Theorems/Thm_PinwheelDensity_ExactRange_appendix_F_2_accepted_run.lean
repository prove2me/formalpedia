-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_appendix_F_2_accepted_run
-- name    : PinwheelDensity.ExactRange.appendix_F_2_accepted_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T20:39:38.52999+00:00
-- url     : https://prove2.me/theorems/9e67b809-9147-4fcb-9888-2d1f187a2c47
-- title:
--   Appendix F.2 — the certificate checker accepts a run for (m, B, θ₀) = (5, 13/15, 12)
-- statement:
--   The proof of Theorems 1.2 and 1.3 (printed p. 17) reads: "Appendix F exhibits accepted runs for $(4, 17/20, 12)$ and $(5, 13/15, 12)$, so Theorem E.1 gives the lower bounds." This statement is the second half of that sentence's premise: some run is accepted for the parameters $m = 5$, $B = 13/15$, $\theta_0 = 12$.
--
--   **Statement.** There is a run $d$ (absorption records and stages $\theta = 12, 14, \dots$, each listing cells with split-tree or absorption certificates and a residual list) with `checkRun ⟨5, 13 / 15, 12⟩ d = true`. Here `checkRun` is the explicit checker of Appendix E (p. 16) as published in the mission's bundle `Def_PinwheelDensity_ExactRange_checkRun`. It recomputes the initial case set $K_{12}$ and every later case set from the residuals, and it accepts only if every case has a valid certificate or is residual, and the last stage has an empty residual. The run itself is only a witness.
--
--   Together with Theorem E.1 (`PinwheelDensity.ExactRange.theorem_E_1`) this gives `Guarantee 5 (13 / 15)`, the lower bound of Theorem 1.3 (`PinwheelDensity.ExactRange.theorem_1_3`).
--
--   **The paper's run.** Appendix F.2 (printed p. 18) describes the run `m5_r1`: 19 stages ($\theta = 12, \dots, 48$) and 386,645 cases. It is deposited with the paper's artifact (Zenodo, https://doi.org/10.5281/zenodo.23406104), as about 2.8 GB of converted Lean data, and the authors accept it stage by stage, with one `native_decide` per stage. That data is far beyond what the verifier can check in the kernel, or the 1 MiB limit on a solution's source, so this statement isolates the computational step as its own node. Its checker agrees clause for clause with the authors' `PWGC.checkAllG` (`lean/PWG/Checker.lean` and `lean/PW2/Checker.lean` in the artifact): the same tree, word, fold and absorption tests, enumerations and stage walk. The authors' checker requires in addition $l^* > 0$ in an absorption record. Absorption cases are looked up by first match here, and by any match there. So a translation of their data, with duplicate case keys removed, is a witness.
-- source:
--   Arisan, Kawamura's pinwheel density conjecture holds for smallest period at most five and fails from six (STOC 2027 submission 387), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/387.pdf, pp. 17–18, proof of Theorems 1.2 and 1.3 and Appendix F.2 (the run m5_r1), data in the artifact https://doi.org/10.5281/zenodo.23406104

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_checkRun

namespace PinwheelDensity.ExactRange

theorem appendix_F_2_accepted_run :
    ∃ d : Run, checkRun ⟨5, 13 / 15, 12⟩ d = true := by sorry

end PinwheelDensity.ExactRange
