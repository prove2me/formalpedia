-- Prove2me | Theorems.Thm_RobustBoolPCSP_Supplement_theorem_6_5
-- name    : RobustBoolPCSP.Supplement.theorem_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:35:53.977002+00:00
-- url     : https://prove2.me/theorems/5e9c2076-e351-4cca-82da-d76e4acb6aa8
-- title:
--   Theorem 6.5 (Balance tester) — dictators pay exactly $\eta$; unbalanced functions pay $\kappa\sqrt\eta/4$
-- statement:
--   Consider the balance tester of §6.1 with parameter $\ell\ge2$, $\eta=9^{-\ell}$, $\beta=\kappa/4$, where $\kappa\in(0,1/12]$ satisfies $3\kappa^{2\gamma-1}\le1/2$ for the absolute constant $\gamma$ of Lemma 6.3. Then, uniformly in the code length $N$:
--
--   1. every dictator $f(X)=X_i$ incurs total strong error mass exactly $\eta$;
--   2. every $f:\{0,1\}^N\to\{0,1\}$ with $\mathbb E_{\mu_0}f\notin[\beta,1-\beta]$ incurs weak error mass at least
--   $$\frac{\kappa\sqrt\eta}{4}$$
--   when the two anchors are correctly pinned.
--
--   The tester has a number of blocks growing like $\log(1/\eta)$ but bounded total mass; it forces long codes to be balanced in the reduction for $T^*$.
--
--   Differences from the source:
--   - reading: κ ∈ (0, 1/12] fixed so small that 3κ^{2γ−1} ≤ 1/2 (52), γ from Lemma 6.3 → ∃ κ₀ ∈ (0, 1/12] such that both bounds hold for every κ ∈ (0, κ₀], with β = κ/4; reason: (52) holds exactly for κ below a threshold depending on the existential γ; every admissible κ is covered
--   - encoding: masses (unnormalized constraint weights) and violation probabilities → testerMass PStar / QStar as finite sums over the sampled strings; reason: exact probabilities on finite spaces
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 6.5, p.47

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_Witness
import Definitions.Def_RobustBoolPCSP_Supplement_BalanceTester

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- **Theorem 6.5 (Balance tester)**, p.47. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Every dictator incurs total strong error mass exactly η. Every Boolean function satisfying
E_{μ0} f ∉ [β, 1 − β] incurs weak error mass at least κ√η/4 when the two anchors are correctly
pinned. Both bounds are uniform in N." Setting: the tester of §6.1 with parameters (53),
"η = 9^{−ℓ}, w = 3^{−ℓ} = √η, L = 2ℓ − 1, r_j = 3^{j−2ℓ} (0 ≤ j ≤ L), β = κ/4", ℓ ≥ 2, where
"Fix κ ∈ (0, 1/12] so small that 3κ^{2γ−1} ≤ 1/2. (52)" with γ the absolute constant of Lemma 6.3.

**Formalization Note.** The tester's masses are `testerMass PStar` (strong) and `testerMass QStar`
(weak), anchors correctly pinned; a dictator is `f(X) = X_i`. Condition (52) holds exactly for
`κ` below a threshold `κ₀` depending on `γ`; the statement asserts the bounds for every
`κ ∈ (0, κ₀]` for some `κ₀ ∈ (0, 1/12]`, with `β = κ/4`. `√η = 3^{−ℓ}`. Uniformity in `N`: the
quantifier over `N` comes after `κ₀`, `κ` and `ℓ`. -/
theorem theorem_6_5 :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ κ₀ ≤ 1 / 12 ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ N : ℕ,
      (∀ i : Fin N, testerMass PStar ℓ N (fun X => X i) = (1 / 9 : ℝ) ^ ℓ) ∧
      ∀ f : (Fin N → Bool) → Bool, (meanMu 0 f < κ / 4 ∨ 1 - κ / 4 < meanMu 0 f) →
        κ * Real.sqrt ((1 / 9 : ℝ) ^ ℓ) / 4 ≤ testerMass QStar ℓ N f := by sorry

end RobustBoolPCSP.Supplement
