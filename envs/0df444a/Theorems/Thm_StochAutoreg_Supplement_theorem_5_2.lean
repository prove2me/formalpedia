-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_5_2
-- name    : StochAutoreg.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:24:24.834241+00:00
-- url     : https://prove2.me/theorems/f633eb44-0804-43cd-8b99-a11dd9b2444a
-- title:
--   Theorem 5.2 — $m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon)\le\frac{40M}{\varepsilon}\bigl(1+m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon/24)\bigr)$
-- statement:
--   Let $\mathcal F$ be any class of generators, $M\ge1$ and $0<\varepsilon\le1$. Then, at confidence $2/3$,
--
--   $$m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon)\le\frac{40M}{\varepsilon}\Bigl(1+m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon/24)\Bigr). \tag{5.3}$$
--
--   End-to-end supervision therefore costs at most a factor $M/\varepsilon$ more than chain-of-thought supervision at a constant multiple of the accuracy, for every class and with explicit constants; Theorem 6.5 shows the factor $M/\varepsilon$ is attained.
--
--   **Formalization Note** When $m_{\mathrm{CoT}}(\varepsilon/24)=n$ is finite (including $n=0$), the conclusion is that $m_{\mathrm{e2e}}(\varepsilon)$ is a natural number $k$ with $k\le(40M/\varepsilon)(1+n)$.
--
--   Differences from the source:
--   - encoding: m(ε) with δ omitted → m(ε, 1/3); reason: p.3: "When δ = 1/3, we omit it"
--   - encoding: sample complexities in {0,1,2,…,+∞} → values in ℕ∞; an upper bound in terms of another complexity is stated for each finite value n of it; reason: when that complexity is +∞ the bound is immediate, as the paper says; ⊤ is never coerced to a real
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 5.2, p.11

import Mathlib
import Definitions.Def_StochAutoreg_mCoT
import Definitions.Def_StochAutoreg_mE2E

namespace StochAutoreg

namespace Supplement

/-- **Theorem 5.2** (from chain-of-thought to end-to-end supervision). For every class `F`, `M ≥ 1`
and `0 < ε ≤ 1`, `m^{F,M}_e2e(ε) ≤ (40M/ε)(1 + m^{F,M}_CoT(ε/24))` (Eq. (5.3)).
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 5.2, Eq. (5.3), p.11.

**Formalization Note.** Both complexities are at confidence `δ = 1/3` (p.3 omits it). The bound is
stated for every finite value `n` of `m_CoT(ε/24)` (`n = 0` included); when `m_CoT(ε/24) = +∞` the
right side is `+∞` and there is nothing to prove, as the paper says. The conclusion says that
`m_e2e(ε)` is a natural number `k` with `k ≤ (40M/ε)(1 + n)`. -/
theorem theorem_5_2 (F : Set Generator) (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ n : ℕ, mCoT F M (ε / 24) (1 / 3) = n →
      ∃ k : ℕ, mE2E F M ε (1 / 3) = k ∧ (k : ℝ) ≤ 40 * M / ε * (1 + n) := by sorry

end Supplement

end StochAutoreg
