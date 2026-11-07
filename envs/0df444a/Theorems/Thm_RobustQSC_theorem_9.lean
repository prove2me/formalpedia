-- Prove2me | Theorems.Thm_RobustQSC_theorem_9
-- name    : RobustQSC.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:45.354051+00:00
-- url     : https://prove2.me/theorems/7883a7ad-7db6-404b-a48c-e053d3cc95dd
-- title:
--   Theorem 9, p.55 — concentration of $\hat M_{\hat f}$ on the small subspace $B$
-- statement:
--   For any $\varepsilon>0$ there is a $T\ge1$ such that with probability $1-\exp(-\Omega_\varepsilon(n))$ over Haar-random $f$,
--
--   $$
--   \|\Pi_B\hat M_{\hat f}\Pi_B\|_{\mathrm{op}}\le\frac12+\varepsilon
--   $$
--
--   and
--
--   $$
--   \|\Pi_A\hat M_{\hat f}\Pi_B\|_{\mathrm{op}}=\|\Pi_B\hat M_{\hat f}\Pi_A\|_{\mathrm{op}}\le\frac14+\varepsilon,
--   $$
--
--   where $\Pi_B$ is the coordinate projection onto $B=B(T)=\{x:\mu_f(x)\notin[1/(TN),T/N]\}$, $\Pi_A$ is onto $A=B^c$, and $N=2^n$. The norm is the $\ell^2$ operator norm.
--
--   These bounds control the contribution of the atypical points, where the net argument is false.
--
--   Differences from the source:
--   - generalization: "there is a $T\ge1$" → there is $T_0\ge1$ such that every $T\ge T_0$ works, with $c_0$ and $n_0$ depending on $\varepsilon$ and $T$; reason: the proof of Theorem 4 (p.73) chooses "$T$ large enough to satisfy the conditions in Theorem 9" and also needs $T\ge12$ for Corollary 6, and Proposition 15 gives smallness of $B$ for every large $T$; the printed statement follows by taking $T=T_0$
--   - reading: the equality in (25) sits inside the probabilistic claim → it is stated for every $f$ and every $T$; reason: $\hat M_{\hat f}$ is Hermitian, so it holds deterministically
--   - encoding: $\Pi_a$ in (25) → $\Pi_A$; reason: misprint of the subscript
--   - encoding: $\|\cdot\|_{\mathrm{op}}$ → the published `specNorm`; reason: the $\ell^2$ operator norm, not the entrywise norm
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), Theorem 9, p.55; M̂, p.56

import Definitions.Def_RobustQSC_mHat
import Definitions.Def_RobustQSC_LocalEscape
import Definitions.Def_RobustQSC_infMu
import Definitions.Def_QAlgorithms_Defs_HaarTargetStates

namespace RobustQSC

open QAlgorithms QAlgorithms.TwoBasisCertification MeasureTheory

/-- **Theorem 9.** For any `ε > 0` there is a `T ≥ 1` such that with probability
`1 − exp(−Ω_ε(n))` over Haar-random `f`, `‖Π_B M̂_f̂ Π_B‖_op ≤ ½ + ε` (24) and
`‖Π_A M̂_f̂ Π_B‖_op = ‖Π_B M̂_f̂ Π_A‖_op ≤ ¼ + ε` (25), where `Π_B` is the coordinate projection onto
`B = B(T) = {x : μ_f(x) ∉ [1/TN, T/N]}` and `Π_A` onto `A = Bᶜ`.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles for
total influence*, arXiv:2607.27184 (sha256 09d2692e…), Theorem 9, p.55; `M̂_f̂`, p.56.

**Formalization Note.**
1. "There is a `T ≥ 1`" is read as "every `T ≥ T₀(ε)`, with some `T₀ ≥ 1`" (the proof of Theorem 4,
   p.73, chooses "T > 0 large enough to satisfy the conditions in Theorem 9"); this implies the
   printed statement. `c₀` (of `Ω_ε`) and `n₀` may depend on `ε` and `T`.
2. The equality in (25) holds for every `f` (`M̂_f̂` is Hermitian) and is stated separately.
3. `‖·‖_op` is the ℓ²-operator norm `specNorm`; `(25)`'s `Π_a` is `Π_A`. -/
theorem theorem_9 :
    (∀ (T : ℝ) (n : ℕ) (f : EuclideanSpace ℂ (Qubits n)),
      specNorm (coordProj (goodSet T (muOf f)) * mHat f * coordProj (goodSet T (muOf f))ᶜ) =
        specNorm (coordProj (goodSet T (muOf f))ᶜ * mHat f * coordProj (goodSet T (muOf f)))) ∧
    ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ n₀ : ℕ,
      ∀ n, n₀ ≤ n →
        haarTargetLaw n {f | IsState f ∧ ¬ (
          specNorm (coordProj (goodSet T (muOf f))ᶜ * mHat f * coordProj (goodSet T (muOf f))ᶜ)
              ≤ 1 / 2 + ε ∧
          specNorm (coordProj (goodSet T (muOf f)) * mHat f * coordProj (goodSet T (muOf f))ᶜ)
              ≤ 1 / 4 + ε)}
          ≤ ENNReal.ofReal (Real.exp (-(c₀ * n))) := by sorry

end RobustQSC
