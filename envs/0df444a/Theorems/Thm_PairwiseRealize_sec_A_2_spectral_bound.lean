-- Prove2me | Theorems.Thm_PairwiseRealize_sec_A_2_spectral_bound
-- name    : PairwiseRealize.sec_A_2_spectral_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:55:40.795197+00:00
-- url     : https://prove2.me/theorems/4b186825-f156-48b1-a1f3-98c72613a61b
-- title:
--   §A.2, p.12 — the spectral bound $\mathbb P(\lambda_{\max}(G)\ge2L)\le m\,e^{(p_*^{-1}-2\log2)L/(4m)}\le m\,e^{-L/(16m)}$
-- statement:
--   Let $p_*=1023/1024$ and $m=1+n+\binom n2$. Let $X_1,\dots,X_K$ be independent random real symmetric positive semidefinite $m\times m$ matrices with $\|X_c\|\le4m$ and $\sum_c\mathbb EX_c\preceq(L/p_*)I_m$, and let $G=\sum_cX_c$. Then
--
--   $$\mathbb P\bigl(\lambda_{\max}(G)\ge2L\bigr)\le m\exp\Bigl(\frac{(p_*^{-1}-2\log2)L}{4m}\Bigr)\le m\,e^{-L/(16m)}.$$
--
--   This keeps the reserve dispersed, so that fixing it at a baseline costs little interior depth.
--
--   Differences from the source:
--   - generalization: G = Σ_C X_C for the reserve bundles, L the reserve size → independent PSD matrices each a function of a uniform draw from a finite nonempty set, L any real; reason: the bundles of the reserve are such draws, by (A.3)
--   - encoding: λmax(G) ≥ 2L → a Rayleigh witness ∃ z ≠ 0, 2L‖z‖² ≤ zᵀGz; probability as a counting ratio; reason: for symmetric G this is the same event
--   - reading: the display ends "= o(1)" → the two inequalities only; reason: o(1) is an asymptotic remark on the size of L, and (A.4) with L ≥ 4C₀mℓ gives it
-- source:
--   Shi, Sun, Robust Exact Realization of Pairwise Boolean Statistics, STOC 2027 submission (sha256 62090516…), §A.2, p.12 (PDF p.13); §3.3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_PairwiseRealize_Model

open scoped Matrix.Norms.L2Operator

namespace PairwiseRealize

open Classical in
/-- **The spectral bound, §A.2 p.12 (PDF p.13); §3.3 p.8 (PDF p.9).** K. Shi, H. Sun, *Robust Exact
Realization of Pairwise Boolean Statistics*, STOC 2027 submission (manuscript sha256 62090516…):
"All bundles, including total triples, have at most four distinct endpoints. Under the independent,
deletion-conditioned law, (A.3) gives µ_max = ‖EG‖ ≤ L/p∗ for G = Σ_C X_C. The matrix exponential
bound underlying matrix Chernoff [Tro12], with θ = (log 2)/(4m), gives
P(λmax(G) ≥ 2L) ≤ m exp((p∗⁻¹ − 2 log 2)L/(4m)) ≤ m e^{−L/(16m)} = o(1)." Here p∗ = 1023/1024.

Let `X_1, …, X_K` be independent random real symmetric positive semidefinite `m × m` matrices
(`m = 1 + n + (n choose 2)`), each with `‖X_c‖ ≤ 4m`, and with `Σ_c E X_c ⪯ (L/p∗) I_m`. Then
`P(λmax(Σ_c X_c) ≥ 2L) ≤ m exp((p∗⁻¹ − 2 log 2)L/(4m)) ≤ m e^{−L/(16m)}`.

**Formalization Note** The law is the paper's: each `X_c` is a function of its own bundle, drawn
from the uniform law on a finite nonempty set `Ω c` (the accepted bundles of its type), and the
bundles are independent, i.e. the uniform law on `Π_c Ω c`; the probability is a counting ratio.
`λmax(G) ≥ 2L` is written as a Rayleigh witness, `∃ z ≠ 0, 2L‖z‖² ≤ zᵀGz`, which for symmetric `G`
is the same event. `‖·‖` is the spectral norm, `⪯` the Loewner order. The `= o(1)` of the display
is the asymptotic remark, not part of the inequality. -/
theorem sec_A_2_spectral_bound (n : ℕ) (K : ℕ) (Ω : Fin K → Type) [∀ c, Fintype (Ω c)]
    [∀ c, Nonempty (Ω c)] (X : (c : Fin K) → Ω c → Matrix (Feat n) (Feat n) ℝ) (L : ℝ)
    (hpsd : ∀ c ω, (X c ω).PosSemidef)
    (hnorm : ∀ c ω, ‖X c ω‖ ≤ 4 * ((1 + n + n.choose 2 : ℕ) : ℝ))
    (hmean : (((L / (1023 / 1024)) • (1 : Matrix (Feat n) (Feat n) ℝ)) -
      ∑ c, ((Fintype.card (Ω c) : ℝ)⁻¹ • ∑ ω : Ω c, X c ω)).PosSemidef) :
    let m : ℝ := ((1 + n + n.choose 2 : ℕ) : ℝ)
    let bad : Finset ((c : Fin K) → Ω c) := Finset.univ.filter fun ω =>
      ∃ z : Feat n → ℝ, z ≠ 0 ∧
        2 * L * (z ⬝ᵥ z) ≤ z ⬝ᵥ ((∑ c, X c (ω c)).mulVec z)
    (bad.card : ℝ) / (Fintype.card ((c : Fin K) → Ω c) : ℝ) ≤
        m * Real.exp (((1023 / 1024 : ℝ)⁻¹ - 2 * Real.log 2) * L / (4 * m)) ∧
      m * Real.exp (((1023 / 1024 : ℝ)⁻¹ - 2 * Real.log 2) * L / (4 * m)) ≤
        m * Real.exp (-L / (16 * m)) := by sorry

end PairwiseRealize
