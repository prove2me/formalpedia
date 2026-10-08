-- Prove2me | Theorems.Thm_ScatCaps_LinearSets_proposition_2_9
-- name    : ScatCaps.LinearSets.proposition_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:59.921454+00:00
-- url     : https://prove2.me/theorems/72d34b88-7a3f-46f2-95c8-46c0a2e1db3e
-- title:
--   Proposition 2.9, p. 15 — for q = 2 some b ∈ 𝔽*_{2^{3n}} satisfies f_{1,1,b}(x)/x ∉ 𝔽_{2^n} for all x ≠ 0
-- statement:
--   Let $n>1$, let $E=\mathbb F_{2^{6n}}$, with subfields $\mathbb F_{2^n}\subseteq\mathbb F_{2^{3n}}$. With $q=2$ and $i=a=1$, the binomial of Proposition 2.7 is $f_{1,1,b}(x)=x^2+bx^{2^{2n+1}}$. There is $b\in\mathbb F_{2^{3n}}^*$ such that
--
--   $$
--   \frac{f_{1,1,b}(x)}{x}\notin\mathbb F_{2^n}\qquad\text{for each }x\in\mathbb F_{2^{3n}}^*.\tag{18}
--   $$
--
--   Together with Proposition 2.7 this produces the $q=2$ family of scattered linear sets (Theorem 2.10).
--
--   **Formalization Note** The printed proposition asserts no norm condition on $b$, and neither does the Lean. $n>1$ is the standing $n\ge2$ of §2.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 15, Proposition 2.9

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.LinearSets

theorem proposition_2_9 (E : Type*) [Field E] [Fintype E]
    (n : ℕ) [ExpChar E 2] (hn : 1 < n)
    (hE : Fintype.card E = 2 ^ (6 * n)) :
    ∃ b : E, b ∈ subfieldOf E 2 1 (3 * n) ∧ b ≠ 0 ∧
      ∀ x : E, x ∈ subfieldOf E 2 1 (3 * n) → x ≠ 0 →
        binom 2 n 1 1 b x / x ∉ subfieldOf E 2 1 n := by sorry

end ScatCaps.LinearSets
