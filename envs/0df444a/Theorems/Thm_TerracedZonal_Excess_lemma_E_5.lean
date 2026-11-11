-- Prove2me | Theorems.Thm_TerracedZonal_Excess_lemma_E_5
-- name    : TerracedZonal.Excess.lemma_E_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:24.090101+00:00
-- url     : https://prove2.me/theorems/7e260b10-5bbc-428c-aa0f-aacc5533ab74
-- title:
--   Lemma E.5 (corrected: remove the window restriction from the continuum minimum) — continuum limit of the terrace cost: $\min G_\lambda=C(\lambda)N^{2/3}(1+o(1))$
-- statement:
--   Fix $\lambda>0$. As $N\to\infty$,
--
--   $$\min_m G_\lambda(m)=C(\lambda)\,N^{2/3}\,(1+o(1)),$$
--
--   where the minimum is over all integer population vectors $m=(m_0,\dots,m_{K-1})$ with every $m_k\ge1$, and the same holds for the minimum under the additional constraint $\sum_k m_k=N-2$. Both minima are attained for all large $N$.
--
--   Here $G_\lambda(m)=\sum_k\psi_{\mathrm{stretch}}(m_k,y_k)+\lambda S(m)$ is the stretching cost plus $\lambda$ times the seam weight, and $C(\lambda)$ is given by (29). The lemma says that the optimal trade-off between stretching inside terraces and seams between them costs $C(\lambda)N^{2/3}$ to leading order.
--
--   Differences from the source:
--   - correction: min_m G_λ(m), with G_λ introduced in (30) "for integer populations m in the window (4)" → the minimum over all integer vectors with every m_k ≥ 1, no window; reason: the explicit window restriction makes the printed claim false, rather than ambiguous; at the fixed price λ = 10^12 every window vector has liminf G_λ/N^{2/3} ≥ λ/80 = 1.25·10^10, whereas C(λ) < 4·10^8 (the counterexample calculation is in HARD.md); removing that restriction only from this continuum minimum preserves all λ > 0, the constant, both mass versions and attainment
--   - encoding: min_m G_λ(m) = C(λ)N^{2/3}(1 + o(1)) → the infimum is asymptotically equivalent (IsEquivalent) to C(λ)N^{2/3}, and it is attained for all sufficiently large N; reason: C(λ) > 0, so asymptotic equivalence is exactly ratio → 1; attainment states that the infimum is the minimum the source writes
--   - encoding: ∑_k m_k = N − 2 → ∑_k m_k + 2 = N in ℕ; reason: avoids truncated subtraction; identical for N ≥ 2
--   - encoding: round(·) with no stated half-integer convention (K, y_k^base, w) → Mathlib's round, half-integers rounded up; reason: the paper fixes no convention; Mathlib round is the standard half-up rounding, and one fixed convention is needed to define the algorithm
--   - reading: K = round((π − 2θ_cap)/h₀) in Algorithm 1a line 1, K = max(1, round(…)) in eq. (18) → K = max(1, round((π − 2θ_cap)/h₀)); reason: the two printed versions differ only when the round is 0 (e.g. N = 3); eq. (18) is the definition and yields at least one ring
-- source:
--   Kabra, Dehaen, Karlova, Hamilton, Carreira, Ovsjanikov, Barron, STOC 2027 submission #638 (October 2026), Lemma E.5, p. 30 (PDF 31)

import Definitions.Def_TerracedZonal_Excess_Rings

namespace TerracedZonal.Excess

open Filter

/-- Lemma E.5, p. 30 (PDF 31): for every fixed `λ > 0`, the minimum of `G_λ` over all integer
population vectors with `m_k ≥ 1` is attained and equals `C(λ) N^{2/3} (1 + o(1))`, both
(a) without and (b) with the constraint `∑_k m_k = N - 2`.
Corrected source domain: (30) restricts populations to the window (4), which makes the
all-`λ > 0` claim false. For fixed `λ = 10^12`, window vectors have asymptotic normalized
cost at least `λ/80 = 1.25 * 10^10`, whereas `C(λ) < 4 * 10^8`; see the counterexample in
the mission's HARD.md. Only this continuum minimum drops the window, not Stage 1. -/
theorem lemma_E_5 (lam : ℝ) (hlam : 0 < lam) :
    (Asymptotics.IsEquivalent atTop (fun N : ℕ => minG lam N)
        (fun N : ℕ => Cfun lam * (N : ℝ) ^ (2 / 3 : ℝ)) ∧
      ∀ᶠ N : ℕ in atTop, ∃ m : Pops N, (∀ k, 1 ≤ m k) ∧ Gcost lam N m = minG lam N) ∧
    (Asymptotics.IsEquivalent atTop (fun N : ℕ => minGMass lam N)
        (fun N : ℕ => Cfun lam * (N : ℝ) ^ (2 / 3 : ℝ)) ∧
      ∀ᶠ N : ℕ in atTop, ∃ m : Pops N, (∀ k, 1 ≤ m k) ∧ ∑ k, m k + 2 = N ∧
        Gcost lam N m = minGMass lam N) := by sorry

end TerracedZonal.Excess
