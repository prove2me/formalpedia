-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_5_5
-- name    : QuantumXoP.Security.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:33.399791+00:00
-- url     : https://prove2.me/theorems/c9c7f1b2-2fdb-4492-8595-75d0898b4954
-- title:
--   Lemma 5.5 — degree-$d$ weight of $\mu_P$
-- statement:
--   For $5\le d\le N/16$,
--   $$\sum_{|\gamma|=d}|\widehat\mu_P(\gamma)|^2\le3^{3d}\Big(\frac Nd\Big)^{\lfloor d/2\rfloor}.$$
--
--   **Formalization Note** $d\le N/16$ is written $16d\le2^n$; $\lfloor d/2\rfloor$ is the natural-number quotient.
--
--   Differences from the source: none.
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 20 (PDF p. 22), Lemma 5.5

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 5.5 (p. 20): for `5 ≤ d ≤ N/16`, `Σ_{|γ|=d} |μ̂_P(γ)|² ≤ 3^{3d} (N/d)^{⌊d/2⌋}`. -/
theorem lemma_5_5 {n d : ℕ} (hd : 5 ≤ d) (hdN : 16 * d ≤ 2 ^ n) :
    ∑ γ ∈ Finset.univ.filter (fun γ : Fn n => charDeg γ = d),
        ‖fourierCoeff (density (permLaw n)) γ‖ ^ 2 ≤
      (3 : ℝ) ^ (3 * d) * (bigN n / d) ^ (d / 2) := by sorry

end QuantumXoP.Security
