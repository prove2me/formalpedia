-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_E_1_two_message_test
-- name    : SpectralFeedback.Supplement.theorem_E_1_two_message_test
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:59:20.306089+00:00
-- url     : https://prove2.me/theorems/34b663d7-94ae-4448-9761-3f9a18ce1ead
-- title:
--   Theorem E.1 — exact two-message ceiling test: pairing of the tail eigenvalues to sum $\tau$
-- statement:
--   Let $\rho$ be a density matrix with $n=\operatorname{rank}\rho$ and $2\le r<n$. Write the least rank-$r$ majorant as
--
--   $$
--   q=(\lambda_1,\dots,\lambda_j,\tau^{[k]},0^{[n-r]}),\qquad k=r-j,\quad N=n-j,\quad \tau=\frac{\sum_{i>j}\lambda_i}{k},
--   $$
--
--   with $j$ chosen minimally, so that every tail eigenvalue $\lambda_{j+1},\dots,\lambda_n$ lies in $(0,\tau]$. Then:
--
--   1. Two symbols attain the unlimited value $\chi(q)$ if and only if $N\le2k$, exactly $2k-N$ tail eigenvalues equal $\tau$, and the remaining $2(N-k)$ tail eigenvalues can be paired so that each pair sums to $\tau$.
--   2. Equivalently, after removing the entries equal to $\tau$, the decreasing remaining list $b_1,\dots,b_{2(N-k)}$ satisfies $b_i+b_{2(N-k)+1-i}=\tau$.
--   3. Whenever the test succeeds, the minimum number of symbols is exactly two (one symbol does not attain $\chi(q)$, because $r<n$), and equal Gram weights suffice: there are $A_1,A_2\succeq0$ with $A_1+A_2=\rho$, $f_r(A_1)+f_r(A_2)=\chi(q)$ and $\operatorname{tr}A_1=\operatorname{tr}A_2=1/2$.
--
--   Differences from the source:
--   - encoding: m symbols attain the unlimited-message value → χ(q) ∈ rewardSet r χ_r m ρ; reason: an attaining decomposition with m atoms, zero atoms allowed
--   - encoding: the remaining tail eigenvalues can be paired → a permutation σ of Fin n that is a fixed-point-free involution on the remaining tail indices with λ_i + λ_σ(i) = τ; reason: a pairing of a set is exactly such an involution
--   - encoding: after removing the entries equal to τ, the decreasing remaining list b_1, …, b_{2(N−k)} → the first 2k − N tail indices carry τ, the indices j + (2k − N) ≤ i < n do not, and b_i = λ at index j + (2k − N) + i − 1; reason: the eigenvalues are decreasing and the tail lies in (0, τ], so the entries equal to τ come first
--   - encoding: equal Gram weights 1/2 → tr A_1 = tr A_2 = 1/2; reason: the Gram weight of an atom is its trace
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem E.1, p.75 (PDF p.77); notation §E.1, p.75

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_Supplement_chi
import Definitions.Def_SpectralFeedback_Supplement_leastMajorant

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem E.1** (Exact two-message ceiling test; Qi, *Spectral Structure and Exact Arithmetic of
Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.75 (PDF p.77)). With the
notation of §E.1 (`n = rank ρ`, `2 ≤ r < n`, least rank-`r` majorant
`q = (λ_1, …, λ_j, τ^{[k]}, 0^{[n−r]})`, `k = r − j`, `N = n − j`, `τ = ∑_{i>j} λ_i / k`, `j`
minimal), two symbols attain the unlimited-message value if and only if `N ≤ 2k`, exactly `2k − N`
tail eigenvalues equal `τ`, and the remaining `2(N − k)` tail eigenvalues can be paired so that each
pair sums to `τ`. Equivalently, after removing the entries equal to `τ`, the decreasing remaining
list `b_1, …, b_{2(N−k)}` satisfies `b_i + b_{2(N−k)+1−i} = τ`. Whenever the test succeeds, the
minimum is exactly two because `r < n`, and equal Gram weights `1/2` suffice.

**Formalization Note** `ρ` is a density matrix (standing assumption of §C.3/§E.1). 0-based: the
tail eigenvalues `λ_{j+1}, …, λ_n` are `eigDesc ρ i` for `j ≤ i < n`. "`m` symbols attain the
unlimited value" is `χ(q) ∈ rewardSet r χ_r m ρ`. A pairing is a permutation `σ` that is a
fixed-point-free involution on the remaining tail indices with `λ_i + λ_{σ(i)} = τ`. In the
"equivalently" form the eigenvalues are already decreasing, so removing the `2k − N` entries equal to
`τ` (the tail lies in `(0, τ]`) leaves the indices `j + (2k − N) ≤ i < n`, and `b_i` (1-based) is
`eigDesc ρ (j + (2k − N) + i − 1)`. "The minimum is exactly two" is: one symbol does not attain the
value. "Equal Gram weights `1/2`" is a two-atom attaining decomposition with `tr A_1 = tr A_2 = 1/2`. -/
theorem theorem_E_1_two_message_test (r : ℕ) (hr : 2 ≤ r) {d : ℕ}
    (ρ : Matrix (Fin d) (Fin d) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) (hrn : r < ρ.rank) :
    let n := ρ.rank
    let lam : ℕ → ℝ := eigDesc ρ
    let j := wfIndex lam n r
    let τ := wfLevel lam n r j
    let k := r - j
    let N := n - j
    let q := leastMajorant lam n r
    let Test : Prop :=
      N ≤ 2 * k ∧
      (Finset.univ.filter (fun i : Fin n => j ≤ (i : ℕ) ∧ lam i = τ)).card = 2 * k - N ∧
      ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n, j ≤ (i : ℕ) → lam i ≠ τ →
        j ≤ (σ i : ℕ) ∧ lam (σ i) ≠ τ ∧ σ i ≠ i ∧ σ (σ i) = i ∧ lam i + lam (σ i) = τ
    let Test' : Prop :=
      N ≤ 2 * k ∧
      (∀ i, j ≤ i → i < j + (2 * k - N) → lam i = τ) ∧
      (∀ i, j + (2 * k - N) ≤ i → i < n → lam i ≠ τ) ∧
      ∀ i, i < 2 * (N - k) →
        lam (j + (2 * k - N) + i) + lam (j + (2 * k - N) + (2 * (N - k) - 1 - i)) = τ
    (chi n q ∈ rewardSet r (chi r) 2 ρ ↔ Test) ∧ (Test ↔ Test') ∧
      (Test → chi n q ∉ rewardSet r (chi r) 1 ρ ∧
        ∃ A₁ A₂ : Matrix (Fin d) (Fin d) ℂ, A₁.PosSemidef ∧ A₂.PosSemidef ∧ A₁ + A₂ = ρ ∧
          reward r (chi r) A₁ + reward r (chi r) A₂ = chi n q ∧
          A₁.trace = 1 / 2 ∧ A₂.trace = 1 / 2) := by sorry

end Supplement

end SpectralFeedback
