-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_3_3
-- name    : QuantumXoP.Security.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:57.795927+00:00
-- url     : https://prove2.me/theorems/b6a2a841-07f9-49a6-bf78-9443b0ffed57
-- title:
--   Lemma 3.3 — density of the XOR of independent random functions
-- statement:
--   Let $D,E$ be distributions on $F_n$ with densities $\mu_D,\mu_E$. Then the convolution $\mu_D*\mu_E$ is the density of the law of $h=f+g$, where $f\leftarrow D$ and $g\leftarrow E$ are independent:
--   $$\mu_D*\mu_E=\mu_{D\oplus E}.$$
--
--   Applied $r-1$ times it shows that $\mu_{XoP[r]}$ is the $r$-fold convolution of $\mu_P$.
--
--   Differences from the source:
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 11 (PDF p. 13), Lemma 3.3

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 3.3 (p. 11): `μ_D ∗ μ_E` is the density of the law of `f + g` for independent
`f ← D`, `g ← E`. -/
theorem lemma_3_3 {n : ℕ} (D E : PMF (Fn n)) :
    conv (density D) (density E) = density (xorLaw D E) := by sorry

end QuantumXoP.Security
