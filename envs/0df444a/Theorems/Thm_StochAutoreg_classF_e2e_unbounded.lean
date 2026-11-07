-- Prove2me | Theorems.Thm_StochAutoreg_classF_e2e_unbounded
-- name    : StochAutoreg.classF_e2e_unbounded
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:09.403214+00:00
-- url     : https://prove2.me/theorems/89311acd-749b-4d5b-8b01-f74db7344d4b
-- title:
--   proof of Theorem 7.1, p.17 — "Lemma 7.2 supplies $D$ with $m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon)>n_0$"
-- statement:
--   With $J$, $M$, $\varepsilon$ and the data of (7.1) as in Lemma 7.2, for every $N\ge1$, every $g_0\in G_N$ and every integer $n_0$, some $D\ge1$ gives
--
--   $$m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon)>n_0$$
--
--   for the combined class $\mathcal F$. Lemma 7.2 is about $H_D$ alone; this is the transfer to $\mathcal F$, which the last step of the proof of Theorem 7.1 uses. It is the numerator of the second ratio.
--
--   Differences from the source:
--   - reading: "Lemma 7.2 supplies D with m_e2e(ε) > n₀", at the fixed ε and N of the proof → one threshold ε₁ depending only on J, and every N ≥ 1, every g₀, every n₀; reason: the same uniformity as Lemma 7.2
--   - generalization: roots placed by one application of Lemma 6.1 → every placement of the combined index set, with D chosen before the placement; reason: it specializes to the source; the proof chooses D without the placement
--   - encoding: m > n₀, with m possibly +∞ → the comparison in ℕ∞; reason: the sample complexity lies in ℕ∞
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, proof of Theorem 7.1, p.17

import Mathlib
import Definitions.Def_StochAutoreg_majF
import Definitions.Def_StochAutoreg_AmpData
import Definitions.Def_StochAutoreg_IsPlacement
import Definitions.Def_StochAutoreg_classF
import Definitions.Def_StochAutoreg_mE2E

namespace StochAutoreg

/-- **The combined end-to-end bound**: "Lemma 7.2 supplies `D` with `m^{F,M}_e2e(ε) > n₀`", for the combined class `F`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, proof of Theorem 7.1, p.17.

**Formalization Note.** Lemma 7.2 is about `H_D` alone; this item is the transfer to `F`. `D` depends on `J, M, ε, N, g₀, n₀` and not on the
placement. -/
theorem classF_e2e_unbounded (J : ℕ) (hJ : Odd J) (hJ' : 200 ≤ deriv (majF J) 0) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ M : ℕ, J + 3 ≤ M → ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      ∀ h tG tH : ℝ, AmpData J ε h tG tH → ∀ N : ℕ, 1 ≤ N →
        ∀ (ω₀ : Fin N → ℤˣ) (τ₀ : ℤˣ) (n₀ : ℕ), ∃ D : ℕ, 1 ≤ D ∧
          ∀ b : (Fin N ⊕ Unit) ⊕ Fin (D + 1) → List Bool, IsPlacement b →
            (n₀ : ℕ∞) < mE2E (classF J M ε tG tH N D ω₀ τ₀ b) M ε (1 / 3) := by sorry

end StochAutoreg
