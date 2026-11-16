-- Prove2me | Theorems.Thm_StochAutoreg_Supplement_theorem_5_4
-- name    : StochAutoreg.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:24:51.536254+00:00
-- url     : https://prove2.me/theorems/a4f9bee4-2bd4-40ab-860e-d4e6e3584bea
-- title:
--   Theorem 5.4 — the end-to-end bound at arbitrary confidence $1-\delta$
-- statement:
--   Let $\mathcal F$ be any class of generators, $M\ge1$, $0<\varepsilon\le1$ and $0<\delta<1$. Let $n=m^{\mathcal F,M}_{\mathrm{CoT}}(\varepsilon/24,1/3)$ and $k=\lceil\log(2/\delta)/\log3\rceil$. Then
--
--   $$m^{\mathcal F,M}_{\mathrm{e2e}}(\varepsilon,\delta)\le kn+\Bigl\lceil\frac{20\log(256/\varepsilon)}{\varepsilon}\Bigl(nM\log2+\log\frac{2k}{\delta}\Bigr)\Bigr\rceil .$$
--
--   The same holds with $n=m^{\mathcal F}_{\mathrm{base}}(\varepsilon/(24M),1/3)$. Logarithms are natural.
--
--   Compared with Theorem 5.2, high confidence costs only logarithmic factors in $1/\delta$ and $1/\varepsilon$.
--
--   **Formalization Note** Both versions are stated, each for every finite value $n$ of its complexity; $k$ is a natural number.
--
--   Differences from the source:
--   - encoding: sample complexities in {0,1,2,…,+∞} → values in ℕ∞; an upper bound in terms of another complexity is stated for each finite value n of it; reason: when that complexity is +∞ the bound is immediate, as the paper says; ⊤ is never coerced to a real
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Theorem 5.4, p.12

import Mathlib
import Definitions.Def_StochAutoreg_mBase
import Definitions.Def_StochAutoreg_mCoT
import Definitions.Def_StochAutoreg_mE2E

namespace StochAutoreg

namespace Supplement

/-- **Theorem 5.4** (arbitrary confidence). For every class `F`, `M ≥ 1`, `0 < ε ≤ 1` and `0 < δ < 1`,
let `n = m^{F,M}_CoT(ε/24, 1/3)` and `k = ⌈log(2/δ)/log 3⌉`. Then
`m^{F,M}_e2e(ε, δ) ≤ kn + ⌈(20 log(256/ε)/ε)(nM log 2 + log(2k/δ))⌉`. The same holds with
`n = m^F_base(ε/(24M), 1/3)`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Theorem 5.4, p.12.

**Formalization Note.** Natural logarithms. Both versions are stated, each for every finite value `n`
of its complexity (for `n = +∞` the bound is immediate, as the paper says). The outer ceiling is the
printed one; `k` is a natural number (`⌈·⌉₊`, at least `1` here). -/
theorem theorem_5_4 (F : Set Generator) (M : ℕ) (hM : 1 ≤ M) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ n : ℕ, mCoT F M (ε / 24) (1 / 3) = n →
      ∃ j : ℕ, mE2E F M ε δ = j ∧
        j ≤ ⌈Real.log (2 / δ) / Real.log 3⌉₊ * n +
          ⌈20 * Real.log (256 / ε) / ε *
            (n * M * Real.log 2 + Real.log (2 * ⌈Real.log (2 / δ) / Real.log 3⌉₊ / δ))⌉₊) ∧
    (∀ n : ℕ, mBase F (ε / (24 * M)) (1 / 3) = n →
      ∃ j : ℕ, mE2E F M ε δ = j ∧
        j ≤ ⌈Real.log (2 / δ) / Real.log 3⌉₊ * n +
          ⌈20 * Real.log (256 / ε) / ε *
            (n * M * Real.log 2 + Real.log (2 * ⌈Real.log (2 / δ) / Real.log 3⌉₊ / δ))⌉₊) := by sorry

end Supplement

end StochAutoreg
