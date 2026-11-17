-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_1_6
-- name    : PermInvCC.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:04:09.542851+00:00
-- url     : https://prove2.me/theorems/f24f02fc-d354-4a4d-9e4a-6bdc1cfab3c8
-- title:
--   Theorem 1.6 — binary fixed-margin simulation: $R^{\mathrm{pub}}(g)=O((Q^*(g)+1)^2)$
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $n \ge 2$, let $a, b \in \{0,\dots,n\}$, and let $g : \{0,1\}^n \times \{0,1\}^n \to \{-1,+1,*\}$ be invariant under simultaneous coordinate permutations, such that every promised input $(x,y)$ satisfies $|x| = a$ and $|y| = b$, where $|\cdot|$ is the Hamming weight. Then
--
--   $$R^{\mathrm{pub}}(g) \le C\,\bigl(Q^*(g) + 1\bigr)^2 .$$
--
--   For binary inputs with fixed weights this removes the logarithmic factor of Theorem 1.1, even for arbitrary promises; Corollary 1.7 follows by exchanging Hamming weights.
--
--   **Formalization Note** $C$ is chosen before $n$, $a$, $b$ and $g$; the Hamming weight of $x$ is the number of coordinates equal to $1$.
--
--   Differences from the source:
--   - encoding: O(·) with an absolute implied constant → ∃ C > 0 chosen before n, a, b, g; reason: the explicit reading of an absolute O-constant
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
--   - encoding: We take n ≥ 2 (p.1) → hypothesis 2 ≤ n; reason: the paper's standing assumption
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 1.6, p.4 (PDF p.7); proof §D.5, p.59 (PDF p.62)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_jointType
import Definitions.Def_PermInvCC_Rpub
import Definitions.Def_PermInvCC_Qstar

namespace PermInvCC

namespace Supplement

/-- **Theorem 1.6 (Binary Fixed-Margin Simulation)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, p.4; proof p.59). Let
`g : {0,1}ⁿ × {0,1}ⁿ → {−1, +1, ∗}` be invariant under simultaneous coordinate permutations, and
suppose every promised input satisfies `|x| = a` and `|y| = b`, for fixed `a, b ∈ {0, …, n}`.
Then `R^pub(g) = O((Q*(g) + 1)²)`, with an absolute implied constant.

**Formalization Note.** The absolute constant `C` is chosen before `n`, `a`, `b`, `g`. Binary
strings are `Fin n → Fin 2` and `|x| = hist x 1`; "promised" means `g x y ≠ none`. `a, b` are
arbitrary in `{0, …, n}` (the normalization `a ≤ b ≤ n/2` is part of the proof). `n ≥ 2` is the
paper's standing assumption. -/
theorem theorem_1_6 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ a b : ℕ, a ≤ n → b ≤ n →
      ∀ g : PartialFn n 2, IsPermInvariant g →
        (∀ x y, g x y ≠ none → hist x 1 = a ∧ hist y 1 = b) →
        (Rpub g : ℝ) ≤ C * ((Qstar g : ℝ) + 1) ^ 2 := by sorry

end Supplement

end PermInvCC
