-- Prove2me | Theorems.Thm_TerracedZonal_Excess_theorem_4_3
-- name    : TerracedZonal.Excess.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:08:06.633918+00:00
-- url     : https://prove2.me/theorems/6c13934f-8075-40b0-adc1-c18798c9cf46
-- title:
--   Theorem 4.3 — under locality (A), $E(X_N)-E_{\mathrm{BHS}}(N)=C_1N^{2/3}+o(N^{2/3})$
-- statement:
--   Let $X_N\subset S^2$ be the configuration produced by TerracedZonal$_0$ with the zonal latitudes $z^{\mathrm{zonal}}$ of (8), i.e. before the four relaxation steps of Stage 2: the poles $(0,0,\pm1)$ and, on ring $k$, $m_k$ equally spaced points at height $z_k$ rotated by the phase $\alpha_k$ of (9), where $m=m_N$ is the output of Stage 1. Assume **locality (A)** for these populations:
--
--   $$E(X_N)-E_{\mathrm{BHS}}(N)=\sum_k\psi_{\mathrm{stretch}}(m_k,y_k)+c_{\mathrm{seam}}\sum_{k:\,m_k\ne m_{k-1}}\tfrac12(y_{k-1}+y_k)+o(N^{2/3}),$$
--
--   i.e. $E(X_N)-E_{\mathrm{BHS}}(N)=G_{c_{\mathrm{seam}}}(m_N)+o(N^{2/3})$. Then $C_1>0$ and
--
--   $$E(X_N)-E_{\mathrm{BHS}}(N)=C_1N^{2/3}+o(N^{2/3}),\qquad C_1=\frac13\Big(1+\frac{2c_{\mathrm{seam}}}{c_{\mathrm{step}}}\Big)C(c_{\mathrm{step}})\approx0.026225,$$
--
--   with $C(\lambda)$ of (29). Here $E$ is the logarithmic energy and $E_{\mathrm{BHS}}(N)$ the Brauchart–Hardin–Saff benchmark. The theorem says the energy gap of this linear-time construction to the conjectured minimum is of order $N^{2/3}$, sublinear in $N$, with an explicit constant; locality (A) is not proved in the paper.
--
--   **Formalization Note** The family $m_N$ is any family of Stage-1 outputs (any tie-break), required for all sufficiently large $N$, and (A) is assumed for that same family.
--
--   Differences from the source:
--   - generalization: (12) for the configurations X_N (the title: Θ(N^{2/3}) excess) → 0 < C₁ ∧ (12); reason: adds the conjunct C₁ > 0, which follows from (29) and makes the Θ of the title explicit; dropping it gives (12)
--   - generalization: the output of the reference implementation (Viterbi arg min and a least-cost repair move, tie-breaks unspecified) → every exact minimizer of G_{c_step} over the window and every admissible least-cost repair choice; reason: the paper fixes no tie-break; the reference implementation is one such choice, so the statement for every choice specializes to it
--   - generalization: the Stage-1 output for every N ≥ 3 → any family m_N that is a Stage-1 output for all sufficiently large N; reason: the conclusion is asymptotic in N; a family that is a Stage-1 output for every N ≥ 3 is in particular eventually one
--   - reading: endpoint peel: the first ring of a terrace of length ≥ 2 changes by sgn(diff) → the peel is allowed only when the peeled ring keeps population ≥ 1; reason: the Ensure line of Algorithm 1a requires every m_k ≥ 1; the paper does not state the guard at the peel; with the guard the loop never stalled in an exhaustive check of all repair choices for 3 ≤ N < 2000 and 150 random N < 2·10⁵
--   - encoding: E(X_N) for the point set X_N → the energy of the indexed family (two poles and the ring points), half the sum over ordered pairs i ≠ j; reason: the points of a Stage-1 configuration are pairwise distinct (strictly decreasing heights in (−1, 1), distinct azimuths on a ring), so both are the sum over unordered pairs
--   - encoding: α_k = (α_{k−1} + 1/(2 lcm(m_{k−1}, m_k))) mod 1 → Int.fract; reason: mod 1 of a nonnegative real is its fractional part
--   - encoding: round(·) with no stated half-integer convention (K, y_k^base, w) → Mathlib's round, half-integers rounded up; reason: the paper fixes no convention; Mathlib round is the standard half-up rounding, and one fixed convention is needed to define the algorithm
--   - reading: K = round((π − 2θ_cap)/h₀) in Algorithm 1a line 1, K = max(1, round(…)) in eq. (18) → K = max(1, round((π − 2θ_cap)/h₀)); reason: the two printed versions differ only when the round is 0 (e.g. N = 3); eq. (18) is the definition and yields at least one ring
--   - encoding: ∑_k m_k = N − 2 → ∑_k m_k + 2 = N in ℕ; reason: avoids truncated subtraction; identical for N ≥ 2
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), Theorem 4.3, p. 10 (PDF 11); locality (A), p. 10 (PDF 11); constant (29), p. 29 (PDF 30)

import Definitions.Def_TerracedZonal_Excess_Config

namespace TerracedZonal.Excess

open Filter

/-- Theorem 4.3, p. 10 (PDF 11), with `C₁` of (29). Let `m_N` be, for all large `N`, a
population vector produced by Stage 1 of TerracedZonal₀, and `X_N = config N (m_N)` the
configuration with the zonal latitudes (8) (no relaxation), phases (9) and coordinates (22).
Assume locality (A) for this family:
`E(X_N) - E_BHS(N) = G_{c_seam}(m_N) + o(N^{2/3})`.
Then `C₁ > 0` and `E(X_N) - E_BHS(N) = C₁ N^{2/3} + o(N^{2/3})`. -/
theorem theorem_4_3 (m : ∀ N : ℕ, Pops N)
    (hm : ∀ᶠ N : ℕ in atTop, IsStage1Output N (m N))
    (hA : (fun N : ℕ => logEnergy (config N (m N)) - E_BHS N - Gcost cSeam N (m N)) =o[atTop]
      (fun N : ℕ => (N : ℝ) ^ (2 / 3 : ℝ))) :
    0 < C1 ∧
    (fun N : ℕ => logEnergy (config N (m N)) - E_BHS N - C1 * (N : ℝ) ^ (2 / 3 : ℝ)) =o[atTop]
      (fun N : ℕ => (N : ℝ) ^ (2 / 3 : ℝ)) := by sorry

end TerracedZonal.Excess
