-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_5_6
-- name    : QuantumXoP.Security.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:48.457432+00:00
-- url     : https://prove2.me/theorems/1986dabb-3011-4851-9afe-f14b24e0f6fb
-- title:
--   Lemma 5.6 — high-degree weights of $\mu_{XoP[r]}$
-- statement:
--   Let $r\ge2$, $r\le N/16$ (the standing assumption of §5) and $5\le d_{\max}\le N/28887$. Then
--   $$\|\mu^{=6}_{XoP[r]}\|_2^2\le3^{18}2^3\Big(\frac{12}N\Big)^{6r-9},\qquad \|\mu^{=5}_{XoP[r]}\|_2^2+\sum_{d=7}^{d_{\max}}\|\mu^{=d}_{XoP[r]}\|_2^2\le3^{22}2^{11}\Big(\frac{10}N\Big)^{6r-8},$$
--   and $\|\mu^{=6}_{XoP[r]}\|_2^2=O(1/N^{6r-9})$, with a constant depending only on $r$.
--
--   These are the high-degree cases of Lemma 5.2.
--
--   **Formalization Note** The two explicit bounds are kept with the printed constants. The section's standing assumption $r\le N/16$ is a hypothesis.
--
--   Differences from the source:
--   - reading: printed with r ≥ 2 only; §5 assumes 2 ≤ r ≤ N/16 throughout (p. 14) → 16r ≤ 2^n; reason: the standing assumption of §5 is a hypothesis of every result of the section
--   - reading: O(·), the hidden factor depending only on r (abstract; p. 14; p. 34) → ∃ C > 0, quantified after r and before n, q, the workspace, the algorithm and the output map; reason: the paper fixes what the hidden constant may depend on
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 20 (PDF p. 22), Lemma 5.6, with the §5 standing assumption (p. 14)

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 5.6 (p. 20): for `r ≥ 2` and `5 ≤ d_max ≤ N/28887`,
`‖μ^{=6}_{XoP[r]}‖₂² ≤ 3^{18} 2^3 (12/N)^{6r−9}`,
`‖μ^{=5}_{XoP[r]}‖₂² + Σ_{d=7}^{d_max} ‖μ^{=d}_{XoP[r]}‖₂² ≤ 3^{22} 2^{11} (10/N)^{6r−8}`, and
`‖μ^{=6}_{XoP[r]}‖₂² = O(1/N^{6r−9})` with a constant depending only on `r`; under the standing
assumption `r ≤ N/16` of §5 (p. 14). -/
theorem lemma_5_6 (r : ℕ) (hr : 2 ≤ r) :
    (∃ C : ℝ, 0 < C ∧ ∀ n dmax : ℕ, 16 * r ≤ 2 ^ n → 5 ≤ dmax → 28887 * dmax ≤ 2 ^ n →
      l2norm (degComp (density (xopLaw n r)) 6) ^ 2 ≤ C / bigN n ^ (6 * r - 9)) ∧
    ∀ n dmax : ℕ, 16 * r ≤ 2 ^ n → 5 ≤ dmax → 28887 * dmax ≤ 2 ^ n →
      l2norm (degComp (density (xopLaw n r)) 6) ^ 2 ≤ (3 : ℝ) ^ 18 * 2 ^ 3 * (12 / bigN n) ^ (6 * r - 9) ∧
      l2norm (degComp (density (xopLaw n r)) 5) ^ 2 +
          ∑ d ∈ Finset.Icc 7 dmax, l2norm (degComp (density (xopLaw n r)) d) ^ 2 ≤
        (3 : ℝ) ^ 22 * 2 ^ 11 * (10 / bigN n) ^ (6 * r - 8) := by sorry

end QuantumXoP.Security
