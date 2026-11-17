-- Prove2me | Theorems.Thm_SpencerEight_Supplement_theorem_15_10
-- name    : SpencerEight.Supplement.theorem_15_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:54:09.681827+00:00
-- url     : https://prove2.me/theorems/e1634e9a-7305-43f2-af4f-a08688c89978
-- title:
--   Theorem 15.10 — existence at $2-\delta$ — a signed-permutation family with every signing of norm above $(2-\delta)\sqrt n+1$
-- statement:
--   Let $n\ge4$ be even. Suppose there are an integer $p\ge1$ and numbers $\gamma\in(0,1/2]$, $s_0>0$ and $\delta\in(0,2)$ such that, with
--   $$
--   \eta_0:=2\gamma+(1+\gamma)\frac{6}{\sqrt{\log(1+\gamma)}}\sqrt{\frac{\log n}{n}},\qquad M:=2+\eta_0+\sqrt{32\pi/n}+s_0,
--   $$
--   where $ns_0M>16(2p-1)$ is required,
--   $$
--   T:=2M^{2p}e^{-ns_0^2/32}\Bigl[1+\frac{32p}{ns_0M-16(2p-1)}\Bigr],\qquad B:=C_p\prod_{j=1}^p\Bigl(1-\frac jn\Bigr)-T-(2-\delta)^{2p}>0,\qquad L:=\frac{(M-2+\delta)B}{2M^{2p}},
--   $$
--   one has
--   $$
--   L-\frac{\sqrt{32\pi}}{n}>\sqrt{\frac{32\log2}{n}}.\tag{249}
--   $$
--   Then there exist real symmetric signed permutation matrices $A_1,\dots,A_n\in\mathbb R^{n\times n}$ with $A_i^2=I_n$, so $\|A_i\|=1$ exactly, such that
--   $$
--   \Bigl\|\sum_{i=1}^n\varepsilon_iA_i\Bigr\|>(2-\delta)\sqrt n+1\qquad\text{for every }\varepsilon\in\{-1,1\}^n.
--   $$
--   Here $C_p=\frac{(2p)!}{p!(p+1)!}$ is the Catalan number and $\log$ is the natural logarithm.
--
--   This finite-$n$ criterion is the source of the asymptotic lower constant $2$ for Matrix Spencer: the admissible $\delta$ tend to $0$ as $n\to\infty$.
--
--   **Formalization Note** $C_p$ is Mathlib's `catalan p`; the parameters are local definitions in the statement. In (249) the root on the left covers $32\pi$ only, as printed, while in $M$ it covers $32\pi/n$.
--
--   Differences from the source:
--   - encoding: indices 1, …, n; ε ∈ {−1, 1}ⁿ → Fin n; real ε i with ε i = 1 ∨ ε i = −1; reason: indexing and the embedding of the signs in ℝ; same instances
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Theorem 15.10, pp.295-296 (PDF pp.295-296)

import Mathlib
import Definitions.Def_SpencerEight_signedSum
import Definitions.Def_SpencerEight_Supplement_IsSignedPerm
open scoped Matrix.Norms.L2Operator

namespace SpencerEight.Supplement

/-- Theorem 15.10 (Existence at `2 − δ`), Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), pp.295-296 (PDF pp.295-296). Let `n ≥ 4` be
even, `p ≥ 1` an integer, `γ ∈ (0, 1/2]`, `s₀ > 0`, `δ ∈ (0, 2)`, and put
`η₀ := 2γ + (1+γ)·6/√(log(1+γ))·√(log n / n)`, `M := 2 + η₀ + √(32π/n) + s₀` (with `n s₀ M > 16(2p−1)`
required), `T := 2M^{2p} e^{−n s₀²/32} [1 + 32p/(n s₀ M − 16(2p−1))]`,
`B := C_p ∏_{j=1}^p (1 − j/n) − T − (2−δ)^{2p}` (required `> 0`), `L := (M − 2 + δ) B / (2M^{2p})`.
If `L − √(32π)/n > √(32 log 2 / n)` (249), then there are real symmetric signed permutation matrices
`A₁, …, A_n ∈ ℝ^{n×n}` with `Aᵢ² = I_n`, so `‖Aᵢ‖ = 1`, such that `‖∑ᵢ εᵢ Aᵢ‖ > (2 − δ)√n + 1` for every
`ε ∈ {−1,1}ⁿ`.

**Formalization Note** `log` is the natural logarithm `Real.log`; `C_p` is Mathlib's `catalan p`
(`= (2p)!/(p!(p+1)!)`); `2p − 1` is computed in `ℝ`. In (249) the square root on the left covers `32π` only
(`√(32π)/n`), as printed, while in `M` it covers `32π/n`. The norm is the L2 operator norm and the signs are
the reals `1` and `-1`. -/
theorem theorem_15_10 (n : ℕ) (hn : 4 ≤ n) (hev : Even n) (p : ℕ) (hp : 1 ≤ p)
    (γ s₀ δ : ℝ) (hγ : 0 < γ ∧ γ ≤ 1 / 2) (hs₀ : 0 < s₀) (hδ : 0 < δ ∧ δ < 2) :
    let η₀ : ℝ := 2 * γ + (1 + γ) * (6 / Real.sqrt (Real.log (1 + γ))) *
      Real.sqrt (Real.log n / n)
    let M : ℝ := 2 + η₀ + Real.sqrt (32 * Real.pi / n) + s₀
    let T : ℝ := 2 * M ^ (2 * p) * Real.exp (-(n * s₀ ^ 2) / 32) *
      (1 + 32 * p / (n * s₀ * M - 16 * (2 * (p : ℝ) - 1)))
    let B : ℝ := (catalan p : ℝ) * ∏ j ∈ Finset.Icc 1 p, (1 - (j : ℝ) / n) - T - (2 - δ) ^ (2 * p)
    let L : ℝ := (M - 2 + δ) * B / (2 * M ^ (2 * p))
    16 * (2 * (p : ℝ) - 1) < n * s₀ * M →
    0 < B →
    Real.sqrt (32 * Real.log 2 / n) < L - Real.sqrt (32 * Real.pi) / n →
    ∃ A : Fin n → Matrix (Fin n) (Fin n) ℝ,
      (∀ i, (A i).IsSymm ∧ IsSignedPerm (A i) ∧ A i * A i = 1 ∧ ‖A i‖ = 1) ∧
      ∀ ε : Fin n → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) →
        (2 - δ) * Real.sqrt n + 1 < ‖signedSum A ε‖ := by sorry

end SpencerEight.Supplement
