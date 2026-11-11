-- Prove2me | Theorems.Thm_QNoiseStab_proposition_3_2
-- name    : QNoiseStab.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:51.935705+00:00
-- url     : https://prove2.me/theorems/7935d3e7-5982-453d-9ca2-cbeb595e4382
-- title:
--   Proposition 3.2 — $\Pr[N_p^A(x)=y]=\langle y|T_p^A|x\rangle=(1-p+\tfrac pm)^{|A|-d_A}(\tfrac pm)^{d_A}$
-- statement:
--   Let $m\ge1$, $A\subseteq[n]$, $p\in\mathbb R$ and $x,y\in\mathbb Z_m^{\,n}$. Write $d_A(x,y)=\sum_{i\in A}(1-\delta_{x_i,y_i})$. Then:
--
--   1. $\Pr[N_p^A(x)=y]=\langle y|\,T_p^A\,|x\rangle$;
--   2. if $x_{[n]\setminus A}=y_{[n]\setminus A}$, then
--   $$
--   \Pr\bigl[N_p^A(x)=y\bigr]=\Bigl(1-p+\frac pm\Bigr)^{|A|-d_A(x,y)}\Bigl(\frac pm\Bigr)^{d_A(x,y)},
--   $$
--   and $d_A(x,y)=d(x,y)$ is the Hamming distance between $x$ and $y$;
--   3. if $x_{[n]\setminus A}\neq y_{[n]\setminus A}$, then $\Pr[N_p^A(x)=y]=0$.
--
--   It identifies the restricted noise operator, written in the Fourier basis, with the classical noise kernel in the standard basis.
--
--   Differences from the source:
--   - generalization: $p$ a resampling probability → every real $p$; reason: all three parts are identities in $p$; the source's $p\in[0,1]$ is a special case
--   - encoding: $\Pr[N_p^A(x)=y]$, $\langle y|T_p^A|x\rangle$, $d(x,y)$ → `noiseKernel p A x y`, the matrix entry `noiseOp p A y x`, Mathlib's `hammingDist x y`; reason: the law of the random variable, the matrix entry and the Hamming distance are the same numbers
--   - encoding: $x_{[n]\setminus A}=y_{[n]\setminus A}$ and its negation; $|A|-d_A$ → `∀ i ∉ A, x i = y i` and `∃ i ∉ A, x i ≠ y i`; natural-number subtraction; reason: same conditions; $d_A\le|A|$, so the subtraction is exact
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Proposition 3.2, p.12

import Mathlib
import Definitions.Def_QNoiseStab_noiseKernel
import Definitions.Def_QNoiseStab_noiseOp

namespace QNoiseStab

/-- **Proposition 3.2** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query
Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256
814fe20e…), p.12). Let `x, y ∈ [m]ⁿ`. Then `Pr[N_p^A(x) = y] = ⟨y| T_p^A |x⟩`; if
`x_{[n]∖A} = y_{[n]∖A}` then
`Pr[N_p^A(x) = y] = (1 − p + p/m)^{|A| − d_A(x,y)} (p/m)^{d_A(x,y)}`, where
`d_A(x, y) = Σ_{i∈A} (1 − δ_{x_i,y_i}) = d(x, y)` is the Hamming distance between `x_A` and `y_A`;
when `x_{[n]∖A} ≠ y_{[n]∖A}`, `Pr[N_p^A(x) = y] = 0`.

**Formalization Note** `[m]` is `ZMod m`; `Pr[N_p^A(x) = y]` is `noiseKernel p A x y`; the matrix
entry `⟨y|T_p^A|x⟩` is `noiseOp p A y x`. `d_A(x, y)` is the number of `i ∈ A` with `x_i ≠ y_i`, so
the natural-number subtraction `|A| − d_A` is exact. The identities hold for every real `p`. -/
theorem proposition_3_2 {n m : ℕ} [NeZero m] (p : ℝ) (A : Finset (Fin n))
    (x y : Fin n → ZMod m) :
    let dA : ℕ := (A.filter fun i => x i ≠ y i).card
    ((noiseKernel p A x y : ℝ) : ℂ) = noiseOp p A y x ∧
      ((∀ i, i ∉ A → x i = y i) →
        noiseKernel p A x y = (1 - p + p / m) ^ (A.card - dA) * (p / m) ^ dA ∧
          dA = hammingDist x y) ∧
      ((∃ i, i ∉ A ∧ x i ≠ y i) → noiseKernel p A x y = 0) := by sorry

end QNoiseStab
