-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_lemma_6_3
-- name    : RandProdExp.TwoSided.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:22:10.139309+00:00
-- url     : https://prove2.me/theorems/332d3548-9efd-4616-b94c-e78c1abe10f5
-- title:
--   Lemma 6.3 — $\Pr_\sigma[\tau_M\text{ injective}]\ge1-C_{D,\rho,\varepsilon}$ over the reals
-- statement:
--   Let $D\ge1$, $\rho\in(0,1)$, $\varepsilon\in(0,2^{-D})$ and $n\ge N_{D,\varepsilon}=\max\{16(192D/e)^{24},(2^D\varepsilon)^{-2}\}$. Fix an $\varepsilon$-closed set $M\subseteq[n]^D$ and dimensions $\rho n\le k_i\le n$. Then in the real Rademacher model
--   $$\Pr_\sigma\big[\tau_M\text{ injective}\big]\ge1-C_{D,\rho,\varepsilon},\qquad C_{D,\rho,\varepsilon}=2(4C_\rho)^D\Big(1+\frac4\rho\Big)^D\sqrt{2^D\varepsilon},\quad C_\rho=3(1+\rho^{-1/2}).$$
--   For the parameters of Equation (16) the bound is at least $1/2$, so real sign witnesses exist.
--
--   Differences from the source:
--   - encoding: D ∈ ℕ → D : ℕ with 1 ≤ D; reason: standing assumption D ≥ 1 of §3.1 (p. 19)
--   - encoding: Pr over independent uniform signs; τ_M := β̄^G_M injective (Definition 6.2) → uniform counting probability over sign tuples (signProb) of BarInjective at the normalized matrices; reason: finitely many equally likely sign tuples; injectivity of β̄ is ker β ⊆ Im α
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 35, Lemma 6.3

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Diagram
import Definitions.Def_RandProdExp_TwoSided_RealModel
import Definitions.Def_RandProdExp_TwoSided_Params

namespace RandProdExp.TwoSided

/-- **Lemma 6.3** (p. 35). For `D ∈ ℕ` (`D ≥ 1`), `ρ ∈ (0, 1)`, `ε ∈ (0, 2^{−D})`, and
`n ≥ N_{D,ε} = max{16 (192 D / e)^{24}, (2^D ε)^{−2}}`, fix an ε-closed set `M ⊆ [n]^D` and dimensions
`ρ n ≤ k_i ≤ n`. Then in the real Rademacher model,
`Pr_σ[τ_M injective] ≥ 1 − C_{D,ρ,ε}`, `C_{D,ρ,ε} = 2 (4 C_ρ)^D (1 + 4/ρ)^D √(2^D ε)`,
`C_ρ = 3 (1 + ρ^{−1/2})`. -/
theorem lemma_6_3 (D : ℕ) (hD : 1 ≤ D) (ρ ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hε0 : 0 < ε) (hε1 : ε < (2 : ℝ) ^ (-(D : ℤ))) (n : ℕ) (hn : NDeps D ε ≤ n)
    (M : Set (Fin D → Fin n)) (hM : IsEpsClosed ε M) (k : Fin D → ℕ)
    (hk : ∀ i, ρ * n ≤ k i ∧ k i ≤ n) :
    1 - CDrhoEps D ρ ε ≤ signProb (fun σ : SignTuple k n => RealTauInjective M σ) := by sorry

end RandProdExp.TwoSided
