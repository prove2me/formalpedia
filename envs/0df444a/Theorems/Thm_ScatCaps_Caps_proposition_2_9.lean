-- Prove2me | Theorems.Thm_ScatCaps_Caps_proposition_2_9
-- name    : ScatCaps.Caps.proposition_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:03.314661+00:00
-- url     : https://prove2.me/theorems/c249b155-46b8-4a90-b6e3-35315d483af4
-- title:
--   Proposition 2.9, p. 15 — for q = 2 some b ∈ 𝔽*_{2^{3n}} has f_{1,1,b}(x)/x ∉ 𝔽_{2^n} for every x ∈ 𝔽*_{2^{3n}}
-- statement:
--   Let $n \ge 2$ and $q = 2$, and let $f_{1,1,b}(x) = x^2 + b x^{2^{2n+1}}$ be the binomial of Proposition 2.7 with $i = a = 1$. There exists $b \in \mathbb F^*_{2^{3n}}$ such that
--
--   $$\frac{f_{1,1,b}(x)}{x} \notin \mathbb F_{2^n} \quad \text{for each } x \in \mathbb F^*_{2^{3n}} . \tag{18}$$
--
--   Condition (18) is the hypothesis on $b$ in Theorem 2.10.
--
--   **Formalization Note** The bound $n \ge 2$ is the standing assumption of Section 2 (p. 4). The fields $\mathbb F_{2^n} \subseteq \mathbb F_{2^{3n}}$ are realized inside an ambient $E$ with $|E| = 2^{6n}$ of characteristic 2.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 15, Proposition 2.9 (eq. (18), (19))

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.Caps

theorem proposition_2_9 (E : Type*) [Field E] [Fintype E] [CharP E 2] (n : ℕ) (hn : 2 ≤ n)
    (hE : Fintype.card E = 2 ^ (6 * n)) :
    ∃ b ∈ ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n), b ≠ 0 ∧
      ∀ x ∈ ScatCaps.LinearSets.subfieldOf E 2 1 (3 * n), x ≠ 0 →
        ScatCaps.LinearSets.binom 2 n 1 1 b x / x ∉ ScatCaps.LinearSets.subfieldOf E 2 1 n := by sorry

end ScatCaps.Caps
