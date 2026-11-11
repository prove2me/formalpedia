-- Prove2me | Theorems.Thm_QuantumXoP_Security_lemma_3_2
-- name    : QuantumXoP.Security.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:05:20.430278+00:00
-- url     : https://prove2.me/theorems/8274880a-7cb6-430d-a252-e57d7f2a1a68
-- title:
--   Lemma 3.2 — convolution theorem $\widehat{H*G}=\widehat H\,\widehat G$
-- statement:
--   For functionals $H,G:F_n\to\mathbb C$ and every $\gamma\in\widehat F$,
--   $$\widehat{H*G}(\gamma)=\widehat H(\gamma)\,\widehat G(\gamma).$$
--
--   With Lemma 3.3 it gives $\widehat\mu_{XoP[r]}(\gamma)=\widehat\mu_P(\gamma)^r$ (Eq. (15)).
--
--   Differences from the source:
--   - generalization: n is a fixed positive integer (§2, p. 8) → every n : ℕ, including n = 0; reason: the case n = 0 is one extra instance; the statement specializes to every n ≥ 1
-- source:
--   Wonseok Choi, Minki Hhan, Junyoung Jang, Quantum Security of XOR of Permutations via Fourier Analysis, STOC 2027 submission #815 (October 2026), p. 11 (PDF p. 13), Lemma 3.2

import Mathlib
import Definitions.Def_QuantumXoP_Security_Fourier

namespace QuantumXoP.Security

open QAlgorithms
open scoped ComplexConjugate

/-- Lemma 3.2 (p. 11): the convolution theorem `(H ∗ G)^(γ) = Ĥ(γ) Ĝ(γ)`. -/
theorem lemma_3_2 {n : ℕ} (H G : Fn n → ℂ) (γ : Fn n) :
    fourierCoeff (conv H G) γ = fourierCoeff H γ * fourierCoeff G γ := by sorry

end QuantumXoP.Security
