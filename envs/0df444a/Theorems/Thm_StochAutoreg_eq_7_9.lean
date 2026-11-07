-- Prove2me | Theorems.Thm_StochAutoreg_eq_7_9
-- name    : StochAutoreg.eq_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:26:24.823667+00:00
-- url     : https://prove2.me/theorems/6d107bd6-d0b0-4f97-a5de-9f8e55159faa
-- title:
--   Eq. (7.9) — $c_1N/\varepsilon\le m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon)\le C_1N/\varepsilon$, independently of $D$
-- statement:
--   Fix $J$ as in (7.1). There are constants $c_1,C_1>0$ such that for all sufficiently small $\varepsilon$ with the data of (7.1), $M\ge J+3$, $N,D\ge1$ and $g_0\in G_N$, the combined class satisfies
--
--   $$\frac{c_1N}\varepsilon\le m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon)\le\frac{C_1N}\varepsilon.$$
--
--   The constants do not depend on $D$, which is what separates chain-of-thoughts from end-to-end supervision on this class. This is the numerator of the first ratio of Theorem 7.1 and the denominator of the second.
--
--   Differences from the source:
--   - reading: constants c₁, C₁ > 0, for sufficiently small ε → c₁, C₁, ε₁ chosen before ε, M, N, D, g₀ and the placement, with the complexity a natural number; reason: this is the uniformity the proof gives and the theorem uses, and (7.7)'s remark on N, D applies
--   - generalization: roots placed by one application of Lemma 6.1 → every placement of the combined index set; reason: it specializes to the source; the construction uses only distinctness and equal length
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, proof of Theorem 7.1, Eq. (7.9), p.17

import Mathlib
import Definitions.Def_StochAutoreg_majF
import Definitions.Def_StochAutoreg_AmpData
import Definitions.Def_StochAutoreg_IsPlacement
import Definitions.Def_StochAutoreg_classF
import Definitions.Def_StochAutoreg_mCoT

namespace StochAutoreg

/-- **Eq. (7.9)**: `c₁N/ε ≤ m^{F,M}_CoT(ε) ≤ C₁N/ε`, with constants not depending on `N, D, M, ε`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, proof of Theorem 7.1, Eq. (7.9), p.17.

**Formalization Note.** The independence is the order of the quantifiers; the complexity is a natural number. -/
theorem eq_7_9 (J : ℕ) (hJ : Odd J) (hJ' : 200 ≤ deriv (majF J) 0) :
    ∃ c₁ C₁ ε₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < ε₁ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ h tG tH : ℝ, AmpData J ε h tG tH →
        ∀ M : ℕ, J + 3 ≤ M → ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
          ∀ (ω₀ : Fin N → ℤˣ) (τ₀ : ℤˣ) (b : (Fin N ⊕ Unit) ⊕ Fin (D + 1) → List Bool), IsPlacement b →
            ∃ d : ℕ, mCoT (classF J M ε tG tH N D ω₀ τ₀ b) M ε (1 / 3) = d ∧
              c₁ * N / ε ≤ d ∧ (d : ℝ) ≤ C₁ * N / ε := by sorry

end StochAutoreg
