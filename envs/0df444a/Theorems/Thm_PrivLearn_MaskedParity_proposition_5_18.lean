-- Prove2me | Theorems.Thm_PrivLearn_MaskedParity_proposition_5_18
-- name    : PrivLearn.MaskedParity.proposition_5_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:47:32.61877+00:00
-- url     : https://prove2.me/theorems/82be27d2-b454-4ab7-9da2-1ebe87efb17d
-- title:
--   Proposition 5.18 — A_MP learns MASKED-PARITY exactly in 2 rounds with d+1 queries of tolerance ≥ 1/(4d+1)
-- statement:
--   Let $d$ be a power of two and let examples be uniform on $D=\{0,1\}^d\times\{0,1\}^{\log d}\times\{0,1\}$. The learner $\mathcal A_{\mathrm{MP}}$ makes $d$ first-round queries with tolerance $\frac1{4d+1}$ and one second-round query with tolerance $\frac15$, so every tolerance is at least $\frac1{4d+1}$. For every target $c_{r,a}$, every valid answers $\mathit{answer}_1,\dots,\mathit{answer}_d$ of the SQ oracle to the first-round queries, and every valid answer $\mathit{answer}_{d+1}$ to the second-round query (the one built from those first-round answers),
--   $$\hat r=r,\qquad \hat a=a,\qquad \mathcal A_{\mathrm{MP}}\text{ outputs } c_{\hat r,\hat a}=c_{r,a}.$$
--
--   This is part (1) of Theorem 5.16 in detail: an adaptive SQ learner recovers the target exactly, with probability $1$, from $d+1$ queries in two rounds.
--
--   **Formalization Note.** "With probability 1" is read as: for every valid answers of the oracle, which is how an SQ algorithm is analysed (the oracle is adversarial within the tolerance). "Efficiently" (running time $O(d)$) is not modelled. "$d+1$ queries in 2 rounds" is the shape of the learner ($d$ then $1$).
-- source:
--   Kasiviswanathan, Lee, Nissim, Raskhodnikova and Smith, What Can We Learn Privately?, arXiv:0803.0924v3, p. 28, Proposition 5.18

import Mathlib
import Definitions.Def_PrivLearn_MaskedParity_Model
import Definitions.Def_PrivLearn_MaskedParity_AMP

namespace PrivLearn.MaskedParity

/-- **Proposition 5.18** (p. 28). Let `d` be a power of two. The two-round learner `A_MP` makes
`d + 1` queries with tolerances at least `1/(4d+1)`, and for every target `c_{r,a}` and every valid
answers of the SQ oracle (first round: to `g_j` with tolerance `1/(4d+1)`; second round: to the
query `g_{d+1}` built from the first-round answers, with tolerance `1/5`) it recovers `r̂ = r`,
`â = a`, and outputs the target concept `c_{r,a}` itself. -/
theorem proposition_5_18 {d : ℕ} (hd : ∃ m : ℕ, d = 2 ^ m) :
    (∀ j, 1 / (4 * (d : ℝ) + 1) ≤ (AMP d).τ₁ j) ∧
    (∀ ans k, 1 / (4 * (d : ℝ) + 1) ≤ (AMP d).τ₂ ans k) ∧
    ∀ (r : Fin d → ZMod 2) (a : ZMod 2) (ans₁ : Fin d → ℝ) (ans₂ : Fin 1 → ℝ),
      (∀ j, IsLabeledSQAnswer (cMP r a) ((AMP d).q₁ j) ((AMP d).τ₁ j) (ans₁ j)) →
      (∀ k, IsLabeledSQAnswer (cMP r a) ((AMP d).q₂ ans₁ k) ((AMP d).τ₂ ans₁ k) (ans₂ k)) →
      rhat ans₁ = r ∧ ahat (ans₂ 0) = a ∧ (AMP d).out ans₁ ans₂ = cMP r a := by sorry

end PrivLearn.MaskedParity
