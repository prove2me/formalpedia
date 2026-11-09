-- Prove2me | Theorems.Thm_RSCapacity_lemma_4_3
-- name    : RSCapacity.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:56.876649+00:00
-- url     : https://prove2.me/theorems/9d219592-b76b-449b-924b-eb497c7bdee4
-- title:
--   Lemma 4.3 (Dimension lower bound for $\mathcal Q$)
-- statement:
--   Fix $u_0>1$ and $1<s<u_0$, and put $\Delta=u_0-s$ and $\bar\Delta=\min\{1,\Delta\}$. Let $1\le r<K\le A$ be integers, $1<c<s$, and let $\mathcal T,\mathcal Q$ be built from $(A,K,r,m,c,s)$. Whenever
--   $$u=\frac{A}{K-1}\ge u_0\qquad\text{and}\qquad \bar\Delta m\ge2,$$
--   we have
--   $$\dim\mathcal Q\ \ge\ \frac{\bar\Delta^3}{8192}\,|\mathcal T|\,(K-1)\,m^3 .$$
--   In particular there is an absolute constant $\kappa>0$ such that, for fixed $u_0>s>1$, $\dim\mathcal Q\ge a_0|\mathcal T|(K-1)m^3$ for all sufficiently large $m$, with $a_0=\kappa\min\{1,u_0-s\}^3$.
--
--   This is the dimension side of the dimension–rank comparison that produces the interpolant.
--
--   Differences from the source:
--   - reading: a_0 = Ω(min{1, u_0 − s}³) for all sufficiently large m → ∃ absolute κ > 0 with a_0 = κ·min{1, u_0 − s}³, and a threshold m_0 chosen after u_0, s and before F, A, K, r, c; reason: the standard meaning of Ω with a constant independent of u_0, s
--   - encoding: dim 𝒬 → Module.finrank F 𝒬; reason: 𝒬 is spanned by finitely many monomials, so finrank is its dimension
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 4.3, p.14 (PDF 16)

import Mathlib
import Definitions.Def_RSCapacity_InterpSpace

set_option autoImplicit false

namespace RSCapacity

/-- **Lemma 4.3 (Dimension lower bound).** Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 4.3, p.14
(PDF 16). Fix u_0 > 1 and 1 < s < u_0, and put Δ := u_0 − s, Δ̄ := min{1, Δ}. Whenever
u = A/(K − 1) ≥ u_0 and Δ̄m ≥ 2, dim 𝒬 ≥ (Δ̄³/8192) |𝒯| (K − 1)m³ (25). In particular, for fixed
constants u_0 > s > 1 this gives dim 𝒬 ≥ a_0 |𝒯| (K − 1)m³ for all sufficiently large m, with
a_0 = Ω(min{1, u_0 − s}³).

**Formalization Note.** The standing hypotheses of §4.1 (1 ≤ r < K ≤ A, 1 < c < s) are binders;
s < u follows from s < u_0 ≤ u. The second conjunct is the "in particular": an absolute κ > 0
(chosen first) with a_0 = κ·min{1, u_0 − s}³, and a threshold m_0 depending on u_0, s only. -/
theorem lemma_4_3 :
    (∀ (F : Type) [Field F] (A K r m : ℕ) (c s u₀ : ℝ), 1 ≤ r → r < K → K ≤ A → 1 < u₀ →
      1 < c → c < s → s < u₀ → u₀ ≤ (A : ℝ) / ((K : ℝ) - 1) → 2 ≤ min 1 (u₀ - s) * m →
      min 1 (u₀ - s) ^ 3 / 8192 * ((tailSet r m c s).ncard : ℝ) * ((K : ℝ) - 1) * (m : ℝ) ^ 3 ≤
        (Module.finrank F (interpSpace F A K r m c s) : ℝ)) ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ u₀ s : ℝ, 1 < s → s < u₀ → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ (F : Type) [Field F] (A K r : ℕ) (c : ℝ), 1 ≤ r → r < K → K ≤ A → 1 < c → c < s →
        u₀ ≤ (A : ℝ) / ((K : ℝ) - 1) →
        κ * min 1 (u₀ - s) ^ 3 * ((tailSet r m c s).ncard : ℝ) * ((K : ℝ) - 1) * (m : ℝ) ^ 3 ≤
          (Module.finrank F (interpSpace F A K r m c s) : ℝ)) := by sorry

end RSCapacity
