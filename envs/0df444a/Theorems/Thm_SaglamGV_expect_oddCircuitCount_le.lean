-- Prove2me | Theorems.Thm_SaglamGV_expect_oddCircuitCount_le
-- name    : SaglamGV.expect_oddCircuitCount_le
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:49:00.826198+00:00
-- url     : https://prove2.me/theorems/fa3684b6-6444-4cc9-9c3a-303fd44ef244
-- title:
--   First moment: $\mathbb E Z=\sum_{\ell\text{ odd}}|\mathbb C_\ell|(\tau/V)^{\ell-1}\le\frac V\tau\sum_{\ell\ge3\text{ odd}}\frac{\tau^\ell}{\ell!}p_\ell$
-- statement:
--   Let $d\ge2$, let $M$ be uniform on $\mathbb F_2^{m\times n}$, $\tau=V2^{-m}$, and let $Z$ be the number of odd circuits of $B_d$ contained in $K=\{x\in B_d: Mx=0\}$. Then
--
--   $$
--   \mathbb E Z=\sum_{\substack{3\le\ell\le n+1\\ \ell\text{ odd}}}|\mathbb C_\ell|\Big(\frac\tau V\Big)^{\ell-1}\le\frac V\tau\sum_{\substack{\ell\ge3\\ \ell\text{ odd}}}\frac{\tau^\ell}{\ell!}\,p_\ell .
--   $$
--
--   The right-hand side is the quantity that the paper rewrites as a transition probability of a random walk.
--
--   Differences from the source:
--   - generalization: the chosen m and the regime of §2 → every m ∈ ℕ and every n, d with d ≥ 2; reason: linearity of expectation and the circuit count hold for every m; d ≥ 2 (V ≥ 1) is implied by the regime
--   - encoding: E over M uniform on 𝔽₂^{m×n} → avgM: the average over the 2^{mn} matrices; reason: uniform expectation on a finite set
--   - encoding: the series Σ_{ℓ≥3, ℓ odd} → a tsum over ℓ ∈ ℕ of terms that vanish unless ℓ ≥ 3 is odd; reason: same series; its terms are nonnegative and bounded by τ^ℓ/ℓ!, so it converges
-- source:
--   M. Saglam, Linear codes exceeding the Gilbert–Varshamov bound, STOC 2027 submission manuscript (held version, sha256 ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3), §2, p.3 (display E Z = Σ_{3≤ℓ≤n+1, ℓ odd} |C_ℓ| (τ/V)^{ℓ−1} ≤ (V/τ) Σ_{ℓ≥3, ℓ odd} τ^ℓ p_ℓ/ℓ!)

import Mathlib
import Definitions.Def_SaglamGV_Code
import Definitions.Def_SaglamGV_Params
import Definitions.Def_SaglamGV_Circuit
import Definitions.Def_SaglamGV_Walk

namespace SaglamGV

/-- The first moment of $Z$ (M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*, STOC 2027 submission manuscript (held version, sha256 ac6f2bba…), §2, p.3: "Consequently,
E Z = Σ_{3≤ℓ≤n+1, ℓ odd} |C_ℓ| (τ/V)^{ℓ−1} ≤ (V/τ) Σ_{ℓ≥3, ℓ odd} (τ^ℓ/ℓ!) p_ℓ").

For $M$ uniform on $𝔽_2^{m×n}$, $d ≥ 2$ and $τ = V 2^{−m}$, the expected number $Z$ of odd circuits
of $B_d$ contained in $K = \{x ∈ B_d : Mx = 0\}$ equals the finite sum and is at most the series.

**Formalization Note** Stated for every $m$. The series over odd $ℓ ≥ 3$ is a `tsum` of
nonnegative terms bounded by $τ^ℓ/ℓ!$, hence summable. -/
theorem expect_oddCircuitCount_le (n d m : ℕ) (hd : 2 ≤ d) :
    avgM (fun M : Matrix (Fin m) (Fin n) (ZMod 2) => (oddCircuitCount d M : ℝ)) =
        ∑ ℓ ∈ (Finset.Icc 3 (n + 1)).filter Odd,
          ((circuits n d ℓ).card : ℝ) * (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) ∧
      ∑ ℓ ∈ (Finset.Icc 3 (n + 1)).filter Odd,
          ((circuits n d ℓ).card : ℝ) * (tau n d m / (vol n d : ℝ)) ^ (ℓ - 1) ≤
        (vol n d : ℝ) / tau n d m *
          ∑' ℓ : ℕ, (if 3 ≤ ℓ ∧ Odd ℓ then
            tau n d m ^ ℓ / (ℓ.factorial : ℝ) * zeroSumProb n d ℓ else 0) := by sorry

end SaglamGV
