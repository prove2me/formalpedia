-- Prove2me | Theorems.Thm_TucciCIT_eq_4_8
-- name    : TucciCIT.eq_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:30.184635+00:00
-- url     : https://prove2.me/theorems/6cb20381-0b7b-46b6-a0f3-f8457a1de13c
-- title:
--   Eq. (4.8) — $S_\mu(x:y|e) = H(x:y)$ for $P = |\psi|^2$
-- statement:
--   Let $\psi$ be a unit amplitude, $\sum_{x,y}|\psi(x,y)|^2 = 1$, $\mu$ its meta density matrix and $P(x,y) = |\psi(x,y)|^2$ (4.7). Then
--
--   $$
--   S_\mu(x : y|e) = H(x : y) = \sum_{x,y} P_{xy}\log_2\frac{P_{xy}}{P_{x-}P_{-y}},
--   $$
--
--   the classical mutual information (bits) of the joint law $P$, with marginals $P_{x-} = \sum_y P(x,y)$ and $P_{-y} = \sum_x P(x,y)$ and the convention that terms with $P_{xy} = 0$ vanish.
--
--   This expresses the S-tanglement of the pure meta state through the measured statistics of $\psi$ in the computational basis; it is the quantity compared with $E_F$ in (4.12) and (4.15).
--
--   **Formalization Note** $H(x:y)$ is the published `QAlgorithms.mutualInfoBits`, which is the form printed in eq. (4.11).
--
--   Differences from the source:
--   - encoding: S = von Neumann entropy, logarithms base 2 (eqs. (2.9), (4.11)) → QAlgorithms.vnEntropy (−Re Tr f(ρ), f(t) = t log₂ t, 0 log 0 = 0) of redistributionMarginal partial traces; reason: Lean convention; same values
-- source:
--   Tucci, Quantum Entanglement and Conditional Information Transmission, arXiv:quant-ph/9909041v2, eq. (4.8), p.9, with eqs. (4.7), p.8, and (4.11), p.9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_TucciCIT_metaDensity
import Definitions.Def_TucciCIT_sTanglement
import Definitions.Def_TucciCIT_jointProb

open QAlgorithms

namespace TucciCIT

/-- Tucci, *Quantum Entanglement and Conditional Information Transmission*,
arXiv:quant-ph/9909041v2, eq. (4.8), p.9 (PDF p.9), with eq. (4.7), p.8: "Let
P(x, y) = |ψ(x, y)|². With this P(x, y), one can calculate H(x : y). Eq.(4.6) reduces to
Sµ(x : y|e) = H(x : y)."

For a unit amplitude `ψ` (`Σ_{x,y} |ψ(x,y)|² = 1`), the S-tanglement of its meta density matrix
equals the classical mutual information (bits) of the joint law `P(x, y) = |ψ(x, y)|²`,
`H(x : y) = Σ_{x,y} P_{xy} log₂ (P_{xy} / (P_{x−} P_{−y}))` with `P_{x−} = Σ_y P(x, y)` and
`P_{−y} = Σ_x P(x, y)` (the form printed in eq. (4.11), p.9).

**Formalization Note.** `H(x : y)` is the published `QAlgorithms.mutualInfoBits` of `P` viewed as
a function on `S_x × S_y`; terms with `P_{xy} = 0` contribute `0` (`Real.logb 2 0 = 0`). -/
theorem eq_4_8 {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ψ : Matrix X Y ℂ) (hψ : ∑ x, ∑ y, ‖ψ x y‖ ^ 2 = 1) :
    sTanglement (metaDensity ψ) = mutualInfoBits (fun p : X × Y => jointProb ψ p.1 p.2) := by sorry

end TucciCIT
