-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_D_5
-- name    : PermInvCC.Supplement.theorem_D_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:02:54.139362+00:00
-- url     : https://prove2.me/theorems/219b63d4-c266-4d43-a230-7931af4dcd78
-- title:
--   Theorem D.5 — unbalanced binary margins: $R^{\mathrm{pub}}(g)\le C\min\{a,h_g^{-2}\}\ell$ and $Q^*(g)+1\ge c\,h_g^{-1}\ell$, $\ell=\log(2b/a)$
-- statement:
--   There are absolute constants $C, c, K > 0$ with the following property. Let $n \ge 2$ and let $a, b$ be integers with $1 \le a \le b \le n/2$ and $b \ge 2a$; put $\ell = \log(2b/a)$. Let $g : \{0,1\}^n \times \{0,1\}^n \to \{-1,+1,*\}$ be invariant under simultaneous coordinate permutations, with every promised input satisfying $|x| = a$ and $|y| = b$. If both labels occur among the promised inputs, then
--
--   $$R^{\mathrm{pub}}(g) \le C\,\min\{a,\ h_g^{-2}\}\,\ell, \tag{D.2}$$
--
--   $$Q^*(g) + 1 \ge c\, h_g^{-1}\,\ell, \tag{D.3}$$
--
--   and consequently $R^{\mathrm{pub}}(g) \le K\,(Q^*(g)+1)^2$. Here $h_g$ is the separation parameter of Definition 2.4 and logarithms are base two.
--
--   This is the unbalanced case $b \ge 2a$ of Theorem 1.6: the factor $\ell$ in the classical bound is matched by the quantum lower bound.
--
--   **Formalization Note** "Both labels occur" means that some promised input has value $+1$ and some has value $-1$. All three conclusions are stated.
--
--   Differences from the source:
--   - reading: g of Appendix D (binary, permutation-invariant, promised inputs with |x| = a, |y| = b; §D.1, p.50) → explicit hypotheses IsPermInvariant g and ∀ promised (x, y), hist x 1 = a ∧ hist y 1 = b; reason: the section's standing setting, made explicit; |x| is the number of ones
--   - encoding: absolute constants C, c and the O of "consequently" → ∃ C c K > 0 chosen before n, a, b, g; reason: the explicit reading of absolute constants
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem D.5, eqs. (D.2)–(D.3), p.53 (PDF p.56); setting §D.1, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_hg
import Definitions.Def_PermInvCC_Rpub
import Definitions.Def_PermInvCC_Qstar

namespace PermInvCC

namespace Supplement

/-- **Theorem D.5 (Unbalanced Binary Margins)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, p.53). Here `g` is a binary
permutation-invariant partial function all of whose promised inputs satisfy `|x| = a`,
`|y| = b` (§D.1, p.50). Suppose `1 ≤ a ≤ b ≤ n/2` and `b ≥ 2a`. Let `ℓ = log(2b/a)`. If both
labels occur, then `R^pub(g) ≤ C min{a, h_g^{-2}} ℓ` (D.2) and `Q*(g) + 1 ≥ c h_g^{-1} ℓ` (D.3).
Consequently `R^pub(g) = O((Q*(g) + 1)²)`.

**Formalization Note.** `C`, `c` and the constant `K` of the "consequently" clause are absolute
(chosen before `n, a, b, g`). Binary strings are `Fin n → Fin 2`, `|x| = hist x 1`; `b ≤ n/2` is
`2b ≤ n`. "Both labels occur" means some promised input has value `+1` and some has `−1`. `h_g` is
the base `hg`; logs are base two. The paper's standing assumption `n ≥ 2` is implied by
`2 ≤ 2b ≤ n` and is not repeated. All three conclusions are stated. -/
theorem theorem_D_5 :
    ∃ C c K : ℝ, 0 < C ∧ 0 < c ∧ 0 < K ∧ ∀ n : ℕ, ∀ a b : ℕ, 1 ≤ a → a ≤ b →
      2 * b ≤ n → 2 * a ≤ b →
      ∀ g : PartialFn n 2, IsPermInvariant g →
        (∀ x y, g x y ≠ none → hist x 1 = a ∧ hist y 1 = b) →
        (∃ x y, g x y = some true) → (∃ x y, g x y = some false) →
        (Rpub g : ℝ) ≤ C * min (a : ℝ) ((hg g)⁻¹ ^ 2) * Real.logb 2 (2 * b / a) ∧
        c * (hg g)⁻¹ * Real.logb 2 (2 * b / a) ≤ (Qstar g : ℝ) + 1 ∧
        (Rpub g : ℝ) ≤ K * ((Qstar g : ℝ) + 1) ^ 2 := by sorry

end Supplement

end PermInvCC
