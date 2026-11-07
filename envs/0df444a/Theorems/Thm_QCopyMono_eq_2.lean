-- Prove2me | Theorems.Thm_QCopyMono_eq_2
-- name    : QCopyMono.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:03.720078+00:00
-- url     : https://prove2.me/theorems/c81abc10-6bd0-4424-b161-80d309659bba
-- title:
--   Eq. (2) — $p=\frac1{2n}\big(I[g]-\sum_i\hat g(\{i\})\big)$
-- statement:
--   Let $n\ge1$ and $f:\{0,1\}^n\to\{0,1\}$ with sign representation $g$. The probability $p$ that a uniformly random hypercube edge violates monotonicity satisfies
--   $$
--   p=\frac1{2n}\Big(I[g]-\sum_{i=1}^n\hat g(\{i\})\Big).
--   $$
--   This identity, cited in the paper to [CNS26, Section 2.2], lets the edge tester be run from quantum examples: $I[g]$ is estimated by Fourier sampling and the level-one coefficients by computational-basis samples.
--
--   Differences from the source: none.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.1, p.7, eq. (2)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_Influence

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.1, p.7, eq. (2) (cited there to [CNS26,
Section 2.2]): for `n ≥ 1`, the edge-violation probability is
`p = (1/(2n)) (I[g] − ∑ᵢ ĝ({i}))`.

**Formalization Note.** `I[g]` is `influence f` and `ĝ({i})` is `fourierCoeff f {i}`, both in
the sign representation `0 ↦ 1`, `1 ↦ −1` of input and output. -/
theorem eq_2 (n : ℕ) (hn : 1 ≤ n) (f : Qubits n → Bool) :
    edgeViolProb f = (influence f - ∑ i : Fin n, fourierCoeff f {i}) / (2 * n) := by sorry

end QCopyMono
