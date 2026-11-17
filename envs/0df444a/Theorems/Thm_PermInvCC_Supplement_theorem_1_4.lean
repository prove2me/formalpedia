-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_1_4
-- name    : PermInvCC.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:01:48.20313+00:00
-- url     : https://prove2.me/theorems/cddccb2b-87f4-47cb-b7bd-07a126ef92a8
-- title:
--   Theorem 1.4 — no bound $R^{\mathrm{pub}}(f)\le C\,Q^*(f)^p(\log n)^{1-\delta}$ for binary permutation-invariant $f$
-- statement:
--   Fix real numbers $p \ge 0$ and $\delta \in (0,1]$. There is no constant $C$ such that every binary partial function $f : \{0,1\}^n \times \{0,1\}^n \to \{-1,+1,*\}$ ($n \ge 2$) invariant under simultaneous coordinate permutations and satisfying $Q^*(f) \ge 1$ obeys
--
--   $$R^{\mathrm{pub}}(f) \le C\, Q^*(f)^p\,(\log n)^{1-\delta},$$
--
--   where $Q^*$ is entanglement-assisted quantum communication complexity and logarithms are base two.
--
--   Together with Theorem 1.1, which has the factor $\log(2+n/t)$, this shows that some dependence on the input length is unavoidable in any simulation of this form, however large the power of $Q^*(f)$.
--
--   **Formalization Note** The negated bound ranges over every real $C$ (no sign condition) and every $n \ge 2$; powers with real exponents are real powers.
--
--   Differences from the source:
--   - encoding: binary strings, permutation-invariant (Definition 2.2) → PartialFn n 2 with the base IsPermInvariant (simultaneous permutations); reason: Lean representation of {0,1}^n and Definition 2.2
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
--   - encoding: We take n ≥ 2 (p.1) → hypothesis 2 ≤ n; reason: the paper's standing assumption
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 1.4, p.3 (PDF p.6); restated p.28 (PDF p.31)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_Rpub
import Definitions.Def_PermInvCC_Qstar

namespace PermInvCC

namespace Supplement

/-- **Theorem 1.4 (Lower Bound on Input-Length Dependence)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, p.3; restated p.28). For
every fixed `p ≥ 0` and `δ ∈ (0, 1]`, there is no constant `C` such that all binary
permutation-invariant partial functions `f` with `Q*(f) ≥ 1` satisfy
`R^pub(f) ≤ C Q*(f)^p (log n)^{1−δ}`.

**Formalization Note.** Binary inputs are `Fin n → Fin 2`; permutation invariance is the base
`IsPermInvariant` (simultaneous, Definition 2.2). The negated bound ranges over every `n ≥ 2`
(the paper's standing assumption) and every real `C` (no sign restriction). Powers with real
exponents are `Real.rpow`; logs are base two. -/
theorem theorem_1_4 (p : ℝ) (hp : 0 ≤ p) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ f : PartialFn n 2, IsPermInvariant f → 1 ≤ Qstar f →
      (Rpub f : ℝ) ≤ C * (Qstar f : ℝ) ^ p * Real.logb 2 n ^ (1 - δ) := by sorry

end Supplement

end PermInvCC
