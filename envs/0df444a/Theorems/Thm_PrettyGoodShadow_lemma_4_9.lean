-- Prove2me | Theorems.Thm_PrettyGoodShadow_lemma_4_9
-- name    : PrettyGoodShadow.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:22.453811+00:00
-- url     : https://prove2.me/theorems/d05b00ac-c996-4b84-b390-7fde388d4bc3
-- title:
--   Lemma 4.9 — $\frac1T\sum_{t=T}^{2T-1}\sum_x q_x\Delta_x(p,kt)\le\frac{D(q\|p)+\log2}{T}$
-- statement:
--   Let $p$ and $q$ be priors with $\operatorname{supp}(q)\subseteq\operatorname{supp}(p)$ and let $0\preceq A\preceq I$. For all $k,T\ge1$,
--
--   $$
--   \frac1T\sum_{t=T}^{2T-1}\sum_x q_x\Delta_x(p,kt)\le\frac{D(q\|p)+\log2}{T}.
--   $$
--
--   Random copy numbers enter the analysis here: the average of $\Delta_x$ over $t$ is small even though a single term need not be.
--
--   **Formalization Note** $\Delta_x(p,kt)$ uses $k$ Bernoulli registers and $kt$ copies.
--
--   Differences from the source: none.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Lemma 4.9, p.22 (restated p.24)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_PrettyGoodShadow_Delta
import Definitions.Def_PrettyGoodShadow_labelRelEntropy

namespace PrettyGoodShadow

/-- **Lemma 4.9** (arXiv:2610.06781, sha256 bd055b7d…, p.22, restated p.24). Let `p` and `q` be priors with
`supp(q) ⊆ supp(p)`. Then, for every `k, T ≥ 1`,
`(1/T) Σ_{t=T}^{2T−1} Σ_x q_x Δ_x(p, kt) ≤ (D(q ∥ p) + log 2)/T`.

**Formalization Note** `Δ_x(p, kt)` uses `k` Bernoulli registers and `kt` copies, so the last argument of `Delta` is
the same `k`. `0 ⪯ A ⪯ I` is the standing assumption of §4.1, p.19. -/
theorem lemma_4_9 {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (ρ : L → Matrix d d ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (A : Matrix d d ℂ) (hA : QAlgorithms.IsEffect A)
    (q p : L → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) (hsupp : ∀ x, p x = 0 → q x = 0) (k T : ℕ) (hk : 1 ≤ k) (hT : 1 ≤ T) :
    (T : ℝ)⁻¹ * ∑ t ∈ Finset.Ico T (2 * T), ∑ x, q x * Delta p ρ A (k * t) k x ≤
      (labelRelEntropy q p + Real.log 2) / (T : ℝ) := by sorry

end PrettyGoodShadow
