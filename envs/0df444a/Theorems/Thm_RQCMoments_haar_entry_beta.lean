-- Prove2me | Theorems.Thm_RQCMoments_haar_entry_beta
-- name    : RQCMoments.haar_entry_beta
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T04:10:28.973247+00:00
-- url     : https://prove2.me/theorems/5732dfd5-8450-4725-ba7a-2116ce25a68e
-- title:
--   §2.3 — the Haar entry $|U_{xy}|^2$ has the Porter–Thomas law $\mathrm{Beta}(1,d-1)$
-- statement:
--   Let $d\ge 2$ and let $U$ be a Haar random unitary in $U(d)$. For every row $x$ and column $y$, the squared magnitude of the entry,
--   $$
--   |U_{xy}|^2=|\langle x|U|y\rangle|^2 ,
--   $$
--   has the Porter–Thomas law $\mathrm{Beta}(1,d-1)$, with density $(d-1)(1-u)^{d-2}$ on $(0,1)$.
--
--   This identifies the comparison law in Theorem 4.9 and is the first clause of that theorem.
--
--   Differences from the source:
--
--   - encoding: the law of |U_xy|² under Haar(d), and Beta(1, d−1) → the pushforward (unitaryHaar d).map (entry x y) equals Mathlib's betaMeasure 1 (d − 1) on ℝ; reason: the law of a random variable is the pushforward measure; Beta(1, d−1) is concentrated on (0,1); same statement
--   - reading: a d-dimensional Haar random unitary (no range for d stated) → hypothesis 2 ≤ d; reason: Beta(1, d − 1) is undefined for d = 1, so the sentence concerns d ≥ 2
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), §2.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_RQCMoments_entry
import Definitions.Def_RQCMoments_porterThomas

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- **§2.3, Haar entry law** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), §2.3, p.15, PDF p.17).
For `d ≥ 2` and every entry `(x, y)`, the squared magnitude `|U_{xy}|²` of a Haar random
`U ∈ U(d)` has the Porter–Thomas law `Beta(1, d − 1)`.

**Formalization Note** The law is the pushforward of the Haar probability under the continuous
map `U ↦ |U_{xy}|²`. `d ≥ 2` is the range in which `Beta(1, d − 1)` is defined. -/
theorem haar_entry_beta {d : ℕ} (hd : 2 ≤ d) (x y : Fin d) :
    (QAlgorithms.Schur.unitaryHaar d).map (entry x y) = porterThomas d := by sorry

end RQCMoments
