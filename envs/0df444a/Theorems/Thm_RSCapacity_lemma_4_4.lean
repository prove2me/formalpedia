-- Prove2me | Theorems.Thm_RSCapacity_lemma_4_4
-- name    : RSCapacity.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:28:46.37382+00:00
-- url     : https://prove2.me/theorems/bbaad249-769e-4335-9486-a8fe1b376ebf
-- title:
--   Lemma 4.4 (Uniform parameterized growth bound)
-- statement:
--   Let $J\subset(1,\infty)$ be compact. There are constants $C_J>0$ and $r_J$ such that, for every $r\ge r_J$, every $c\in J$ and every $s>c$, upon setting $m=r^3$,
--   $$\Lambda(W+m)\ \le\ \frac{C_J}{1-c/s}\,|\mathcal T|\,r^{1/c},$$
--   where $W=\lfloor crm/\log(er)\rfloor$ (natural logarithm) and $\mathcal T=\mathcal T(r,m,c,s)$ are those of §4.1.
--
--   The bound compares the tail count after enlarging the weighted cutoff by $m$ with the tail count itself, uniformly over $c\in J$; it controls the rank of one local constraint.
--
--   Differences from the source:
--   - encoding: the real numbers W and ⌈sm⌉ → natural numbers (Nat.floor, Nat.ceil); reason: their arguments are positive for c > 1, r ≥ 1
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), Lemma 4.4, p.16 (PDF 18)

import Mathlib
import Definitions.Def_RSCapacity_InterpSpace

set_option autoImplicit false

namespace RSCapacity

/-- **Lemma 4.4 (Uniform parameterized growth bound).** Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…),
Lemma 4.4, p.16 (PDF 18). Let J ⊂ (1, ∞) be compact. There are constants C_J > 0 and r_J such
that, for every r ≥ r_J, every c ∈ J, and every s > c, upon setting m = r³ we have
Λ(W + m) ≤ (C_J/(1 − c/s)) |𝒯| r^{1/c} (30).

**Formalization Note.** W = ⌊c r m / log(e r)⌋ (natural log) and 𝒯 = 𝒯(r, m, c, s) are those of
§4.1 with m = r³; C_J and r_J are chosen after J and before r, c, s. -/
theorem lemma_4_4 (J : Set ℝ) (hJ : IsCompact J) (hJ1 : J ⊆ Set.Ioi 1) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∃ rJ : ℕ, ∀ r : ℕ, rJ ≤ r → ∀ c ∈ J, ∀ s : ℝ, c < s →
      (Lambda r ((Wcut r (r ^ 3) c + r ^ 3 : ℕ) : ℝ) : ℝ) ≤
        CJ / (1 - c / s) * ((tailSet r (r ^ 3) c s).ncard : ℝ) * (r : ℝ) ^ (1 / c) := by sorry

end RSCapacity
