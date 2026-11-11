-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_lemma_7_1
-- name    : RandProdExp.TwoSided.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:21:27.560015+00:00
-- url     : https://prove2.me/theorems/52b1ae23-bdb8-4464-b003-303f98b1d856
-- title:
--   Lemma 7.1 — $\mathbb E_\sigma\|K\|_{\mathrm{op}}\le C_{D,\rho,\varepsilon}$
-- statement:
--   Let $D\ge1$, $\rho\in(0,1)$, $\varepsilon\in(0,2^{-D})$ and $n\ge N_{D,\varepsilon}=\max\{16(192D/e)^{24},(2^D\varepsilon)^{-2}\}$. Fix an $\varepsilon$-closed set $M\subseteq[n]^D$ and dimensions $\rho n\le k_i\le n$. Then the plane-interaction matrix $K$ of $M$ in the real Rademacher model satisfies
--   $$\mathbb E_\sigma\big[\|K\|_{\mathrm{op}}\big]\le C_{D,\rho,\varepsilon}=2(4C_\rho)^D\Big(1+\frac4\rho\Big)^D\sqrt{2^D\varepsilon},\qquad C_\rho=3(1+\rho^{-1/2}).$$
--   With Markov's inequality and Lemma 6.12 it gives Lemma 6.3.
--
--   Differences from the source:
--   - encoding: D ∈ ℕ → D : ℕ with 1 ≤ D; reason: standing assumption D ≥ 1 of §3.1 (p. 19)
--   - encoding: expectation over independent uniform signs → uniform average over all sign tuples (signAvg); reason: finitely many equally likely sign tuples
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 46, Lemma 7.1

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Diagram
import Definitions.Def_RandProdExp_TwoSided_RealModel
import Definitions.Def_RandProdExp_TwoSided_Params

namespace RandProdExp.TwoSided

/-- **Lemma 7.1** (p. 46). For `D ∈ ℕ` (`D ≥ 1`), `ρ ∈ (0, 1)`, `ε ∈ (0, 2^{−D})`, and
`n ≥ N_{D,ε} = max{16 (192 D / e)^{24}, (2^D ε)^{−2}}`, fix an ε-closed set `M ⊆ [n]^D` and dimensions
`ρ n ≤ k_i ≤ n`. Then the plane-interaction matrix of the real Rademacher model satisfies
`E_σ[‖K‖_op] ≤ C_{D,ρ,ε} = 2 (4 C_ρ)^D (1 + 4/ρ)^D √(2^D ε)`. -/
theorem lemma_7_1 (D : ℕ) (hD : 1 ≤ D) (ρ ε : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hε0 : 0 < ε) (hε1 : ε < (2 : ℝ) ^ (-(D : ℤ))) (n : ℕ) (hn : NDeps D ε ≤ n)
    (M : Set (Fin D → Fin n)) (hM : IsEpsClosed ε M) (k : Fin D → ℕ)
    (hk : ∀ i, ρ * n ≤ k i ∧ k i ≤ n) :
    signAvg (fun σ : SignTuple k n => opNorm (interactionMatrix M σ)) ≤ CDrhoEps D ρ ε := by sorry

end RandProdExp.TwoSided
