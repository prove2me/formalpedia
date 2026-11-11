-- Prove2me | Theorems.Thm_ShamirLLR_eq_75_entropy_bound
-- name    : ShamirLLR.eq_75_entropy_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:26:04.418534+00:00
-- url     : https://prove2.me/theorems/6a91f59a-2e0b-4a8f-8fe9-65a29022f771
-- title:
--   Eq. (75) — binomial entropy bound
-- statement:
--   For $0<\alpha\le1/2$, an integer $t\le\alpha m$ and $x\ge1$,
--   $$
--   \sum_{j<t}\binom mj x^j\le 2^{m\,(h_2(\alpha)+\alpha\log_2x)},
--   $$
--   where $h_2(\alpha)=-\alpha\log_2\alpha-(1-\alpha)\log_2(1-\alpha)$ is the binary entropy.
--
--   The proof of Theorem 1 uses it with $x=2/\tau=\pi$ (Eq. (75)) and §2.1 with $x=2^{3/2}$ (Eq. (11)) to absorb the shortened-tuple terms of Lemma 2.1.
--
--   Differences from the source:
--   - generalization: the instances $x=\pi$ with $t=\lfloor\alpha m\rfloor$ (Eq. (75)) and $x=2^{3/2}$ (Eq. (11)) → every $x\ge1$, $0<\alpha\le1/2$ and integer $t\le\alpha m$; reason: both instances satisfy these conditions ($\alpha<1/4$ in Eq. (74), $\alpha<1/288$ in §2.1)
--   - encoding: $h_2(\alpha)$ in bits → `Real.binEntropy α / Real.log 2`; reason: Mathlib's binary entropy is in nats
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), proof of Theorem 1, Eq. (75), p.65 (PDF p.66); §2.1, Eq. (11), p.15

import Mathlib

set_option autoImplicit false

namespace ShamirLLR

/-- **The binomial entropy bound of Eq. (75)** (and of §2.1, Eq. (11), p.15). For
`0 < α ≤ 1/2`, an integer `t ≤ αm` and `x ≥ 1`,
`∑_{j < t} (m choose j) x^j ≤ 2^{m (h₂(α) + α log₂ x)}`,
where `h₂(α) = −α log₂ α − (1 − α) log₂(1 − α)` is the binary entropy.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
proof of Theorem 1, Eq. (75), p.65 ("the binomial entropy bound is the one used in Section 2");
§2.1, p.15.

**Formalization Note.** `h₂(α) = Real.binEntropy α / log 2` (Mathlib's entropy is in nats). The
paper uses the instances `x = 2^{3/2}` (p.15) and `x = 2/τ = π` (Eq. (75)). -/
theorem eq_75_entropy_bound (m t : ℕ) (α x : ℝ) (hα : 0 < α) (hα2 : α ≤ 1 / 2)
    (ht : (t : ℝ) ≤ α * m) (hx : 1 ≤ x) :
    ∑ j ∈ Finset.range t, (m.choose j : ℝ) * x ^ j ≤
      (2 : ℝ) ^ ((m : ℝ) * (Real.binEntropy α / Real.log 2 + α * Real.logb 2 x)) := by sorry

end ShamirLLR
