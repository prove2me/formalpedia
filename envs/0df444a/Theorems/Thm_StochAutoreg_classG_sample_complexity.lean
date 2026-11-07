-- Prove2me | Theorems.Thm_StochAutoreg_classG_sample_complexity
-- name    : StochAutoreg.classG_sample_complexity
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:25:16.470192+00:00
-- url     : https://prove2.me/theorems/5db701eb-b424-47b0-9a1d-520f6742f94b
-- title:
--   §7, p.15 — final means of $G_N$, $m^{G_N}_{\mathrm{base}}(\varepsilon)=\Theta(1/\varepsilon)$ and $m^{G_N,M}_{\mathrm{CoT}}(\varepsilon)=\Theta(N/\varepsilon)$
-- statement:
--   Fix an odd $J$ with $F_J'(0)\ge200$, sufficiently small $\varepsilon$ with the data of (7.1), $M\ge J+3$, and $N\ge1$. For every $g=g_{\omega,\tau}\in G_N$,
--
--   $$q_g^{\mathrm{e2e}-M}(r_j)=\tfrac12+8\omega_j\sqrt\varepsilon,\qquad q_g^{\mathrm{e2e}-M}(v)=\tfrac12,$$
--
--   and there are constants $c,C>0$ depending only on $J$ with
--
--   $$\frac c\varepsilon\le m^{G_N}_{\mathrm{base}}(\varepsilon)\le\frac C\varepsilon,\qquad\frac{cN}\varepsilon\le m^{G_N,M}_{\mathrm{CoT}}(\varepsilon)\le\frac{CN}\varepsilon.$$
--
--   So base learning is cheap and independent of $N$, while chain-of-thoughts learning costs $N/\varepsilon$.
--
--   Differences from the source:
--   - reading: Θ(1/ε), Θ(N/ε) → explicit c, C > 0 and ε₁ > 0, chosen before ε, M, N and the placement, with both complexities natural numbers; reason: this is the uniformity the proof gives and the theorem uses
--   - generalization: roots placed by Lemma 6.1 → every placement of r₁, …, r_N, v; reason: it specializes to the source; the construction uses only distinctness and equal length
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §7, "The first family G_N", p.15

import Mathlib
import Definitions.Def_StochAutoreg_majF
import Definitions.Def_StochAutoreg_AmpData
import Definitions.Def_StochAutoreg_IsPlacement
import Definitions.Def_StochAutoreg_classG
import Definitions.Def_StochAutoreg_mBase
import Definitions.Def_StochAutoreg_mCoT
import Definitions.Def_StochAutoreg_qE2E
import Definitions.Def_StochAutoreg_root
import Definitions.Def_StochAutoreg_isolate
import Definitions.Def_StochAutoreg_gRule

namespace StochAutoreg

/-- **The bounds for `G_N`**: `q_g^{e2e-M}(r_j) = 1/2 + 8ω_j√ε`, `q_g^{e2e-M}(v) = 1/2`, and `m^{G_N}_base(ε) = Θ(1/ε)`, `m^{G_N,M}_CoT(ε) = Θ(N/ε)`, with constants depending only on `J`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §7 "The first family `G_N`", p.15.

**Formalization Note.** The constants `c, C` and the threshold `ε₁` come before `ε, M, N` and the placement; both complexities are
natural numbers, so the bounds are real comparisons. -/
theorem classG_sample_complexity (J : ℕ) (hJ : Odd J) (hJ' : 200 ≤ deriv (majF J) 0) :
    ∃ c C ε₁ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₁ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ∀ h tG tH : ℝ, AmpData J ε h tG tH →
        ∀ M : ℕ, J + 3 ≤ M → ∀ N : ℕ, 1 ≤ N → ∀ b : Fin N ⊕ Unit → List Bool, IsPlacement b →
          ∃ a d : ℕ,
            mBase (classG J M ε tG b) ε (1 / 3) = a ∧
            mCoT (classG J M ε tG b) M ε (1 / 3) = d ∧
            c / ε ≤ a ∧ (a : ℝ) ≤ C / ε ∧
            c * N / ε ≤ d ∧ (d : ℝ) ≤ C * N / ε ∧
            ∀ (ω : Fin N → ℤˣ) (τ : ℤˣ),
              (∀ j : Fin N, qE2E (isolate M b (gRule J M ε tG ω τ)) M (root b (Sum.inl j)) =
                1 / 2 + 8 * ((ω j : ℤ) : ℝ) * Real.sqrt ε) ∧
              qE2E (isolate M b (gRule J M ε tG ω τ)) M (root b (Sum.inr ())) = 1 / 2 := by sorry

end StochAutoreg
