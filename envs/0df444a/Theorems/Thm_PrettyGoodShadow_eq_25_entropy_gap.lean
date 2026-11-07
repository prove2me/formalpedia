-- Prove2me | Theorems.Thm_PrettyGoodShadow_eq_25_entropy_gap
-- name    : PrettyGoodShadow.eq_25_entropy_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:23.137275+00:00
-- url     : https://prove2.me/theorems/e03095b2-11af-40eb-b068-bd6a0fae4968
-- title:
--   Eq. (25) — $H(S^+(q,s))-H(S(q,s))\le H(\sum_x q_xB_x^{\otimes(s+k)})-H(\sum_x q_xB_x^{\otimes s})$
-- statement:
--   Let $q$ be a prior, $0\preceq A\preceq I$ and $s,k\ge1$. Then
--
--   $$
--   H\big(S^+(q,s)\big)-H\big(S(q,s)\big)\le H\Big(\sum_x q_xB_x^{\otimes(s+k)}\Big)-H\Big(\sum_x q_xB_x^{\otimes s}\Big).
--   $$
--
--   It reduces the quantum entropy gap in Lemma 4.10 to the classical gap of Lemma 4.13.
--
--   **Formalization Note** $H$ is the published von Neumann entropy, in nats.
--
--   Differences from the source:
--   - reading: the display writes B_x^{⊗(n+k)} and B_x^{⊗n} with S⁺(q, s), S(q, s) → n = s throughout; reason: the proof on p.26 uses n and s for the same number, and its conclusion is Lemma 4.10 at s
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), eq. (25), p.26

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_PrettyGoodShadow_Delta

namespace PrettyGoodShadow

open DimFreeShadow (ensembleState)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- **Eq. (25)** (arXiv:2610.06781, sha256 bd055b7d…, p.26). For a prior `q`, an observable `0 ⪯ A ⪯ I` and
`s, k ≥ 1`, `H(S⁺(q, s)) − H(S(q, s)) ≤ H(Σ_x q_x B_x^{⊗(s+k)}) − H(Σ_x q_x B_x^{⊗s})`.

**Formalization Note** `H` is the published von Neumann entropy `entropy` in nats. The letter `n` in the page's
display is `s`: the proof of Lemma 4.10 on p.26 uses both letters for the same number. -/
theorem eq_25_entropy_gap {L d : Type} [Fintype L] [Fintype d] [DecidableEq d]
    (ρ : L → Matrix d d ℂ) (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (A : Matrix d d ℂ)
    (hA : QAlgorithms.IsEffect A) (q : L → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    entropy (Splus q ρ A s k) - entropy (ensembleState q ρ s) ≤
      entropy (bernMix A ρ q (s + k)) - entropy (bernMix A ρ q s) := by sorry

end PrettyGoodShadow
