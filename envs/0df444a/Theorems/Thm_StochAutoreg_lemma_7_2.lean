-- Prove2me | Theorems.Thm_StochAutoreg_lemma_7_2
-- name    : StochAutoreg.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:09.031138+00:00
-- url     : https://prove2.me/theorems/bd753e8e-a3c5-4c0c-a076-e27dcfe5503d
-- title:
--   Lemma 7.2 — $H_D$ under end-to-end supervision: $m^{H_D,M}_{\mathrm{e2e}}(\varepsilon)>n_0$ for some $D$
-- statement:
--   Fix $J$ as in (7.1), $M\ge J+3$, and sufficiently small $\varepsilon>0$. For every integer $n_0\ge0$, some $D\ge1$ satisfies
--
--   $$m^{H_D,M}_{\mathrm{e2e}}(\varepsilon)>n_0.$$
--
--   So at the exact accuracy $\varepsilon$, the sample complexity of end-to-end learning of $H_D$ grows without bound in $D$, although under chain-of-thoughts supervision it is $O(1/\varepsilon)$ uniformly in $D$.
--
--   Differences from the source:
--   - reading: "sufficiently small ε > 0", after M and n₀ are fixed → one threshold ε₁ depending only on J, before M and n₀; reason: the proof's conditions (ε < log 2/8, h_ε small) use neither M nor n₀, and Theorem 7.1's ε₀ is universal
--   - generalization: roots placed by Lemma 6.1 → every placement of x₀, …, x_D, with D chosen before the placement; reason: it specializes to the source; the proof chooses D without the placement
--   - encoding: m > n₀, with m possibly +∞ → the comparison in ℕ∞; reason: the sample complexity lies in ℕ∞
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Lemma 7.2, p.16

import Mathlib
import Definitions.Def_StochAutoreg_majF
import Definitions.Def_StochAutoreg_AmpData
import Definitions.Def_StochAutoreg_IsPlacement
import Definitions.Def_StochAutoreg_classH
import Definitions.Def_StochAutoreg_mE2E

namespace StochAutoreg

/-- **Lemma 7.2**: fix `J` as in (7.1), `M ≥ J + 3`, and sufficiently small `ε > 0`. For every integer `n₀ ≥ 0`, some `D ≥ 1` satisfies
`m^{H_D,M}_e2e(ε) > n₀`. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Lemma 7.2, p.16.

**Formalization Note.** "Sufficiently small" is one threshold `ε₁` depending only on `J`: the proof's conditions (`ε < log 2 / 8`, `h_ε` small) use
neither `M` nor `n₀`, and Theorem 7.1's `ε₀` is universal. `D` does not depend on the placement. -/
theorem lemma_7_2 (J : ℕ) (hJ : Odd J) (hJ' : 200 ≤ deriv (majF J) 0) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ M : ℕ, J + 3 ≤ M → ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
      ∀ h tG tH : ℝ, AmpData J ε h tG tH → ∀ n₀ : ℕ, ∃ D : ℕ, 1 ≤ D ∧
        ∀ b : Fin (D + 1) → List Bool, IsPlacement b →
          (n₀ : ℕ∞) < mE2E (classH J M tH b) M ε (1 / 3) := by sorry

end StochAutoreg
