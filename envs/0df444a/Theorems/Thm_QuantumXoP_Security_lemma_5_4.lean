-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_5_4
-- name    : QuantumXoP.Security.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:27.090862+00:00
-- url     : https://prove2.me/theorems/96747e1d-ec7d-48b1-8ff1-818e5782e26d
-- title:
--   Lemma 5.4 — $M^{=d}[\mu_P]\le(2d/N)^{\lceil d/2\rceil}$
-- statement:
--   Assume $n\ge5$ (the standing assumption of §5). For $1\le d\le N$,
--   $$M^{=d}[\mu_P]=\max_{|\gamma|=d}|\widehat\mu_P(\gamma)|\le\Big(\frac{2d}{N}\Big)^{\lceil d/2\rceil}.$$
--
--   With Lemma 5.5 it bounds the high-degree weights of $\mu_{XoP[r]}=\mu_P^{*r}$ (Lemma 5.6).
--
--   **Formalization Note** $\lceil d/2\rceil$ is the natural number $(d+1)/2$ (integer division).
--
--   Differences from the source:
--   - reading: printed without a condition on n; §5 assumes n ≥ 5 throughout (p. 14) → 5 ≤ n; reason: the standing assumption of §5 is a hypothesis of every result of the section
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 20 (PDF p. 22), Lemma 5.4, with the §5 standing assumption (p. 14)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 5.4 (p. 20): for `1 ≤ d ≤ N`, `M^{=d}[μ_P] ≤ (2d/N)^{⌈d/2⌉}`, under the standing
assumption `n ≥ 5` of §5 (p. 14). -/
theorem lemma_5_4 {n d : ℕ} (hn : 5 ≤ n) (hd : 1 ≤ d) (hdN : d ≤ 2 ^ n) :
    maxMag (density (permLaw n)) d ≤ (2 * (d : ℝ) / bigN n) ^ ((d + 1) / 2) := by sorry

end QuantumXoP.Security
