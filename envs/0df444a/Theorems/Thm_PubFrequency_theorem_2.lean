-- Prove2me | Theorems.Thm_PubFrequency_theorem_2
-- name    : PubFrequency.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:04.070206+00:00
-- url     : https://prove2.me/theorems/f0e23a7d-7e3e-4a11-ba66-789770235014
-- title:
--   Theorem 2, p. 12 — the publishing game has exactly one pair of asymmetric equilibria, given by (11), and the faster publisher earns more
-- statement:
--   Two ex-ante identical information publishers, with information decay rate $\alpha>0$ and fixed publication cost $k>0$ satisfying $\alpha k<1/2$, simultaneously choose publication cycles, each anticipating its pricing-equilibrium profit $\pi(u_i;u_{-i})$; a cycle must be positive and either equal to the rival's or differ from it by a factor of at least $2$ (the publishing game (10)).
--
--   There exist cycles $0<u_1^*<u_2^*$ solving (11),
--   $$u_1^*=\sqrt{\frac{2ku_2^*}{\alpha u_2^*-1}},\qquad u_2^*=\frac{\bigl(\sqrt{6\alpha k+1}+2\bigr)(2-\alpha u_1^*)}{2\alpha(1-2\alpha k)},$$
--   such that:
--   1. the pure-strategy Nash equilibria of the publishing game are **exactly** $(u_1^*,u_2^*)$ and $(u_2^*,u_1^*)$ — a unique pair of asymmetric equilibria, one for each labelling of the firms, and no symmetric equilibrium;
--   2. the faster publisher earns strictly more: $\pi_1^*=\pi(u_1^*;u_2^*)>\pi(u_2^*;u_1^*)=\pi_2^*$.
--
--   Even though the firms are identical, they choose different publication frequencies in equilibrium, which avoids a price war, and the fast publisher has a first-mover advantage.
--
--   **Formalization Note** The paper omits the uniqueness proof (p. ec28); it is part of the statement here.
--
--   Differences from the source:
--   - reading: (10)'s payoff πᵢ(uᵢ; u₋ᵢ) is Firm i's pricing-equilibrium profit Π*ᵢ(u), with the integer-ratio constraint relaxed (p. 12) → pay: the paper's closed-form equilibrium profits at β = 1 for every real pair of positive cycles — Lemma EC.5 if both cycles are ≤ 1/α, (EC.3) if αu_f ≤ 1 < αu_s, (EC.48) if αu_f > 1, and −k/u on equal cycles ((EC.55)); reason: the pricing game needs u₂/u₁ ∈ ℕ and is undefined at the relaxed cycles; the proof of Theorem 3 (pp. ec21–ec22) uses π only through these closed forms; Lemmas EC.2 and EC.5 tie them to the pricing game at integer ratios
--   - reading: at αu_f = 1 both (EC.3) (hypothesis αu₁ ≤ 1) and (EC.48) (hypothesis u₂ ≥ u₁ ≥ 1/α) apply and give different slow-firm profits → the (EC.3)/Lemma EC.5 branch is used whenever αu_f ≤ 1, (EC.48) only when αu_f > 1; reason: this is how the proof of Theorem 3 applies them ((EC.53)–(EC.54) for αu₁ ≤ 1, (EC.48) only to dominate u₁ > 1/α)
--   - reading: 'There exists a unique pair of asymmetric equilibria' → ∀ u₁ u₂, IsPubEq α k u₁ u₂ ↔ (u₁, u₂) = (a, b) ∨ (u₁, u₂) = (b, a); reason: the stronger of the readings: the equilibrium set is exactly the two labellings of one asymmetric profile, so there is no symmetric equilibrium either; the paper omits the uniqueness proof (p. ec28)
--   - reading: u*ᵢ = argmax over the feasible set in (10) → u*ᵢ is a maximizer of its payoff over the feasible set (IsPubEq); reason: the Nash-equilibrium condition; the paper's proof checks only that no feasible deviation is profitable (p. ec28)
--   - encoding: uᵢ > 0 with max{uᵢ, u*₋ᵢ}/min{uᵢ, u*₋ᵢ} ≥ 2 if uᵢ ≠ u*₋ᵢ → Feasible u u' := 0 < u ∧ (u = u' ∨ 2u ≤ u' ∨ 2u' ≤ u); reason: the same set for positive cycles, written without division
--   - encoding: (11) with √ and a division → Real.sqrt (0 on negatives) and real division (x/0 = 0); reason: if αu₂ ≤ 1 the first equation gives u₁ = 0, and then the second gives u₂ ≥ 3/(2α) > 1/α, a contradiction, so no spurious solution appears
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), Theorem 2, eq. (11), p.12 (PDF 13)

import Mathlib
import Definitions.Def_PubFrequency_PublishingGame

namespace PubFrequency

/-- **Theorem 2**, Chen–Roels, *Fast or Slow? Competing on Publication Frequency*, SSRN 3986163
(INSEAD WP 2021/74/TOM), §3.3, p. 12 (PDF 13): "There exists a unique pair of asymmetric
equilibria in the publishing game (10). Denoting Firm 1 as the fastest publisher in equilibrium,
the equilibrium publication cycles solve (11). Moreover, π∗1 > π∗2."

For `α > 0`, `k > 0` with `α k < 1/2` there are cycles `0 < a < b` solving (11),
`a = √(2kb/(αb − 1))`, `b = (√(6αk + 1) + 2)(2 − αa)/(2α(1 − 2αk))`, such that the pure-strategy
equilibria of the publishing game (10) are exactly `(a, b)` and `(b, a)`, and the fast firm earns
strictly more: `pay(b; a) < pay(a; b)`.

**Formalization Note.** The payoffs of (10) are the paper's closed-form pricing-equilibrium
profits at `β = 1` (`pay`); "a unique pair of asymmetric equilibria" is read as: the equilibrium
set is exactly `{(a, b), (b, a)}` (so there is no symmetric equilibrium either). -/
theorem theorem_2 (α k : ℝ) (hα : 0 < α) (hk : 0 < k) (hαk : α * k < 1 / 2) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧
      a = Real.sqrt (2 * k * b / (α * b - 1)) ∧
      b = (Real.sqrt (6 * α * k + 1) + 2) * (2 - α * a) / (2 * α * (1 - 2 * α * k)) ∧
      (∀ u₁ u₂ : ℝ, IsPubEq α k u₁ u₂ ↔ (u₁ = a ∧ u₂ = b) ∨ (u₁ = b ∧ u₂ = a)) ∧
      pay α k b a < pay α k a b := by sorry

end PubFrequency
