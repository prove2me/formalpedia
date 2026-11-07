-- Prove2me | Theorems.Thm_StochAutoreg_eq_7_7
-- name    : StochAutoreg.eq_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:25:54.614066+00:00
-- url     : https://prove2.me/theorems/bfc02678-907c-438f-92da-7f2869988094
-- title:
--   Eq. (7.7) — $c_0/\varepsilon\le m^{\mathcal F}_{\mathrm{base}}(\varepsilon)\le C_0/\varepsilon$, independently of $N,D$
-- statement:
--   Fix $J$ as in (7.1). There are constants $c_0,C_0>0$, independent of $N,D$, such that for all sufficiently small $\varepsilon$ with the data of (7.1), $M\ge J+3$, $N,D\ge1$ and $g_0\in G_N$, the combined class $\mathcal F=\{g\oplus h_0:g\in G_N\}\cup\{g_0\oplus h:h\in H_D\}$ satisfies
--
--   $$\frac{c_0}\varepsilon\le m^{\mathcal F}_{\mathrm{base}}(\varepsilon)\le\frac{C_0}\varepsilon.$$
--
--   This is the denominator of the first ratio of Theorem 7.1.
--
--   Differences from the source:
--   - reading: constants independent of N, D, for sufficiently small ε → c₀, C₀, ε₁ chosen before ε, M, N, D, g₀ and the placement, with the complexity a natural number; reason: this is the uniformity the proof gives and the theorem uses
--   - generalization: roots placed by one application of Lemma 6.1 → every placement of the combined index set; reason: it specializes to the source; the construction uses only distinctness and equal length
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, proof of Theorem 7.1, Eq. (7.7), p.16

import Mathlib
import Definitions.Def_StochAutoreg_majF
import Definitions.Def_StochAutoreg_AmpData
import Definitions.Def_StochAutoreg_IsPlacement
import Definitions.Def_StochAutoreg_classF
import Definitions.Def_StochAutoreg_mBase

namespace StochAutoreg

/-- **Eq. (7.7)**: `c₀/ε ≤ m^F_base(ε) ≤ C₀/ε`, with `c₀, C₀ > 0` independent of `N, D`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, proof of Theorem 7.1, Eq. (7.7), p.16.

**Formalization Note.** Independence of `N, D` is the order of the quantifiers. `g₀ = g_{ω₀,τ₀}` is arbitrary. The complexity is a natural
number. -/
theorem eq_7_7 (J : ℕ) (hJ : Odd J) (hJ' : 200 ≤ deriv (majF J) 0) :
    ∃ c₀ C₀ ε₁ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ 0 < ε₁ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ h tG tH : ℝ, AmpData J ε h tG tH →
        ∀ M : ℕ, J + 3 ≤ M → ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
          ∀ (ω₀ : Fin N → ℤˣ) (τ₀ : ℤˣ) (b : (Fin N ⊕ Unit) ⊕ Fin (D + 1) → List Bool), IsPlacement b →
            ∃ a : ℕ, mBase (classF J M ε tG tH N D ω₀ τ₀ b) ε (1 / 3) = a ∧
              c₀ / ε ≤ a ∧ (a : ℝ) ≤ C₀ / ε := by sorry

end StochAutoreg
