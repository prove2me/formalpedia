-- Prove2me | Theorems.Thm_PubFrequency_eq_EC_6
-- name    : PubFrequency.eq_EC_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:01.491162+00:00
-- url     : https://prove2.me/theorems/9d8ec2d8-6f80-4451-9fdf-bc0c941932c3
-- title:
--   (EC.6), proof of Theorem 2, p. ec3 — the publishing-game payoffs at the solution of (11)
-- statement:
--   Let $\alpha>0$, $k>0$ with $\alpha k<1/2$, and let $(u_1^*,u_2^*)$ with $u_1^*\in[0,1/\alpha]$, $u_2^*\ge0$ solve the system (11). Then the publishing-game payoffs at the profile $(u_1^*,u_2^*)$ are
--   $$\pi_1^*=\pi(u_1^*;u_2^*)=\frac16\Bigl(2\sqrt{6\alpha k+1}-3\alpha u_1^*+2\Bigr)-\frac{k}{u_1^*},\qquad
--   \pi_2^*=\pi(u_2^*;u_1^*)=\frac{2\Bigl(6\alpha k\bigl(\sqrt{6\alpha k+1}-3\bigr)+\sqrt{6\alpha k+1}+1\Bigr)}{27(2-\alpha u_1^*)}.$$
--
--   These closed forms are what the paper compares to show $\pi_1^*>\pi_2^*$.
--
--   Differences from the source:
--   - reading: (10)'s payoff πᵢ(uᵢ; u₋ᵢ) is Firm i's pricing-equilibrium profit Π*ᵢ(u), with the integer-ratio constraint relaxed (p. 12) → pay: the paper's closed-form equilibrium profits at β = 1 for every real pair of positive cycles — Lemma EC.5 if both cycles are ≤ 1/α, (EC.3) if αu_f ≤ 1 < αu_s, (EC.48) if αu_f > 1, and −k/u on equal cycles ((EC.55)); reason: the pricing game needs u₂/u₁ ∈ ℕ and is undefined at the relaxed cycles; the proof of Theorem 3 (pp. ec21–ec22) uses π only through these closed forms; Lemmas EC.2 and EC.5 tie them to the pricing game at integer ratios
--   - reading: (EC.6) is obtained 'by plugging Firm 2's best response in (11) into (EC.3)' at the equilibrium with u∗1 ≤ u∗2 → the identity is stated at every solution (a, b) of (11) with a ∈ [0, 1/α], b ≥ 0 (by Lemma EC.6 the unique one); reason: the derivation uses only (11) and (EC.3); the equilibrium cycles are that solution by Theorem 2
--   - encoding: (11) with √ and a division → Real.sqrt (0 on negatives) and real division (x/0 = 0); reason: if αu₂ ≤ 1 the first equation gives u₁ = 0, and then the second gives u₂ ≥ 3/(2α) > 1/α, a contradiction, so no spurious solution appears
-- source:
--   Chen–Roels, Fast or Slow? Competing on Publication Frequency, SSRN 3986163 (INSEAD WP 2021/74/TOM, 2021), proof of Theorem 2, eq. (EC.6), p.ec3 (PDF 32)

import Mathlib
import Definitions.Def_PubFrequency_PublishingGame

namespace PubFrequency

/-- **Equilibrium profits (EC.6)**, Chen–Roels, *Fast or Slow? Competing on Publication
Frequency*, SSRN 3986163 (INSEAD WP 2021/74/TOM), proof of Theorem 2, p. ec3 (PDF 32). Let
`α > 0`, `k > 0` with `α k < 1/2`, and let `(a, b)` with `a ∈ [0, 1/α]`, `b ≥ 0` solve (11). Then the
publishing-game payoffs at the profile `(a, b)` are
`π₁* = pay(a; b) = (1/6)(2√(6αk + 1) − 3αa + 2) − k/a` and
`π₂* = pay(b; a) = 2(6αk(√(6αk + 1) − 3) + √(6αk + 1) + 1)/(27(2 − αa))`.

**Formalization Note.** `pay` is the closed-form payoff of the publishing game (10); this item
states that, evaluated at the solution of (11), it equals (EC.6). -/
theorem eq_EC_6 (α k : ℝ) (hα : 0 < α) (hk : 0 < k) (hαk : α * k < 1 / 2) (a b : ℝ)
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1 / α) (hb : 0 ≤ b)
    (h₁ : a = Real.sqrt (2 * k * b / (α * b - 1)))
    (h₂ : b = (Real.sqrt (6 * α * k + 1) + 2) * (2 - α * a) / (2 * α * (1 - 2 * α * k))) :
    pay α k a b = 1 / 6 * (2 * Real.sqrt (6 * α * k + 1) - 3 * α * a + 2) - k / a ∧
    pay α k b a = 2 * (6 * α * k * (Real.sqrt (6 * α * k + 1) - 3) + Real.sqrt (6 * α * k + 1) + 1)
      / (27 * (2 - α * a)) := by sorry

end PubFrequency
