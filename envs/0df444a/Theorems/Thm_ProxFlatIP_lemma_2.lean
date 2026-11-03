-- Prove2me | Theorems.Thm_ProxFlatIP_lemma_2
-- name    : ProxFlatIP.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:25.589297+00:00
-- url     : https://prove2.me/theorems/f191076b-24bc-450f-b57a-18ef352219b9
-- title:
--   Lemma 2 — $\kappa_n(\alpha)<2^{n-1}\|\alpha\|_2/(\mathrm{vol}_{n-1}(P_\alpha)\Delta^\alpha)$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ have full column rank, $b\in\mathbb Z^m$, and $P=P(A,b)$. Let $\alpha\in\mathbb Z^n$ be nonzero, and assume $\dim P=n$ and $P\cap\mathbb Z^n=\{0\}$. Then
--   $$\kappa_n(\alpha)<\frac{2^{n-1}\,\|\alpha\|_2}{\mathrm{vol}_{n-1}(P_\alpha)\,\Delta^\alpha}.$$
--
--   This turns a lower bound on the volume of the section $P_\alpha$ into an upper bound on $\kappa_n$. Integrality of $b$ is essential here (Remark 2, p.7).
--
--   **Formalization Note** The volume $\mathrm{vol}_{n-1}(P_\alpha)$ is finite and positive, as $P_\alpha$ is bounded and $(n-1)$-dimensional for $A$ of full column rank and $\alpha\neq0$. Neither fact is a hypothesis.
--
--   Differences from the source:
--   - encoding: vol_{n−1}(P_α) as a real number → the real value (.toReal) of the measure in ℝ≥0∞; reason: the measure is finite here, so no value changes
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, Lemma 2, p.6

import Mathlib
import Definitions.Def_ProxFlatIP_Kappa

open Matrix

namespace ProxFlatIP

/-- **Lemma 2** (arXiv:2211.14941v1, Lemma 2, p.6). Let `α ∈ ℤⁿ` be nonzero, `dim P = n` and
`P ∩ ℤⁿ = {0}`. Then `κ_n(α) < 2^{n−1} ‖α‖₂ / (vol_{n−1}(P_α) Δ^α)`.

**Formalization Note.** `vol_{n−1}(P_α)` is finite and positive, because `P_α` is bounded and
`(n−1)`-dimensional for `A` of full column rank and `α ≠ 0`; so `.toReal` loses nothing, and neither
fact is a hypothesis. `n ≥ 1` follows from `α ≠ 0`, so `n − 1` is not truncated. -/
theorem lemma_2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : FullColRank A) (b : Fin m → ℤ)
    (α : Fin n → ℤ) (hα : α ≠ 0) (hdim : dimLin (Poly A b) = n)
    (hP : Poly A b ∩ {x | IsIntegralPt x} = {0}) :
    kappaD A b α n <
      2 ^ (n - 1) * ‖euclidVec α‖ /
        ((volHyper α (Palpha A α)).toReal * (deltaAlpha A α : ℝ)) := by sorry

end ProxFlatIP
