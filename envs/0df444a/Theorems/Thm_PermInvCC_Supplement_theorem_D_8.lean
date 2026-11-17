-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_D_8
-- name    : PermInvCC.Supplement.theorem_D_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:03:38.914879+00:00
-- url     : https://prove2.me/theorems/50fce906-d2af-49df-8ecb-e8b991062e14
-- title:
--   Theorem D.8 — comparable binary margins: $R^{\mathrm{pub}}(g)=O(h_g^{-2}+\log(B+2))$
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $n \ge 2$ and let $a, b$ be integers with $1 \le a \le b \le n/2$ and $b < 2a$. Let $g : \{0,1\}^n \times \{0,1\}^n \to \{-1,+1,*\}$ be a binary permutation-invariant partial function with fixed weights $a, b$, i.e. every promised input satisfies $|x| = a$ and $|y| = b$. Then
--
--   $$R^{\mathrm{pub}}(g) \le C\,\bigl(h_g^{-2} + \log(B+2)\bigr),$$
--
--   where $h_g$ is the separation parameter of Definition 2.4 and $B$ is the number of label changes between consecutive points of the ordered set of promised intersection counts $|x \cap y|$. Logarithms are base two.
--
--   This is the comparable case $b < 2a$ of Theorem 1.6; with Lemma D.10 it gives the purely quadratic simulation.
--
--   **Formalization Note** There is no "both labels occur" hypothesis, as on the page.
--
--   Differences from the source:
--   - reading: g of Appendix D (binary, permutation-invariant, promised inputs with |x| = a, |y| = b; §D.1, p.50) → explicit hypotheses IsPermInvariant g and ∀ promised (x, y), hist x 1 = a ∧ hist y 1 = b; reason: the section's standing setting, made explicit; |x| is the number of ones
--   - encoding: O(·) (absolute constant) → ∃ C > 0 chosen before n, a, b, g; reason: the explicit reading of an absolute O-constant
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem D.8, p.55 (PDF p.58); B defined §D.1, p.51 (PDF p.54)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_hg
import Definitions.Def_PermInvCC_Rpub
import Definitions.Def_PermInvCC_Supplement_labelChanges

namespace PermInvCC

namespace Supplement

/-- **Theorem D.8 (Comparable Binary Margins)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, p.55). Let `g` be a binary
permutation-invariant partial function with fixed weights `1 ≤ a ≤ b ≤ n/2` and `b < 2a`. Then
`R^pub(g) = O(h_g^{-2} + log(B + 2))`, where `B` is the number of changes of label between
consecutive points in the ordered domain of the intersection-count label function (p.51).

**Formalization Note.** The constant `C` is absolute (chosen before `n, a, b, g`). "Fixed
weights" means every promised input has `|x| = a`, `|y| = b` (`|x| = hist x 1`, §D.1); `b ≤ n/2`
is `2b ≤ n`. `B` is `labelChanges g`, `h_g` the base `hg` (`= 1` when at most one label
occurs); logs are base two. There is no "both labels occur" hypothesis, as on the page. The
standing assumption `n ≥ 2` follows from `1 ≤ a ≤ b` and `2b ≤ n` and is not repeated. -/
theorem theorem_D_8 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ a b : ℕ, 1 ≤ a → a ≤ b → 2 * b ≤ n → b < 2 * a →
      ∀ g : PartialFn n 2, IsPermInvariant g →
        (∀ x y, g x y ≠ none → hist x 1 = a ∧ hist y 1 = b) →
        (Rpub g : ℝ) ≤ C * ((hg g)⁻¹ ^ 2 + Real.logb 2 ((labelChanges g : ℝ) + 2)) := by sorry

end Supplement

end PermInvCC
