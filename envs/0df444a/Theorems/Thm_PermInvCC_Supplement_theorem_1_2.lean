-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_1_2
-- name    : PermInvCC.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:58:38.671811+00:00
-- url     : https://prove2.me/theorems/4ed44a61-64e2-42e0-8073-44218f6b88b5
-- title:
--   Theorem 1.2 — quantum characterization: $c_qM(f)\le Q^*(f)+1\le Q(f)+1\le C_q\min\{n,M(f)\log n\}$
-- statement:
--   Fix an alphabet size $q \ge 2$. For a partial function $f : [q]^n \times [q]^n \to \{-1,+1,*\}$ invariant under simultaneous coordinate permutations, let
--
--   $$M(f) := \max_{\rho,\sigma} h_{f_{\rho,\sigma}}^{-1},$$
--
--   the maximum over all pairs of nonnegative integer histograms $\rho, \sigma$ of total $n$ of the inverse separation parameter of the fixed-margin restriction $f_{\rho,\sigma}$ (a restriction with at most one promised label has $h_{f_{\rho,\sigma}} = 1$). Then there are constants $c_q, C_q > 0$, depending only on $q$, such that for every $n \ge 2$ and every such $f$,
--
--   $$c_q\,M(f) \;\le\; Q^*(f) + 1 \;\le\; Q(f) + 1 \;\le\; C_q \min\{n,\ M(f)\log n\},$$
--
--   where $Q$ is quantum communication complexity without prior entanglement and $Q^*$ the entanglement-assisted one; logarithms are base two.
--
--   The theorem characterizes the quantum communication complexity of fixed-alphabet permutation-invariant functions by $M(f)$ up to a logarithmic factor, and shows that prior entanglement can be removed at a multiplicative cost $O_q(\log n)$.
--
--   **Formalization Note** $c_q, C_q$ are chosen after $q$ and before $n$ and $f$. All three inequalities of the chain are stated.
--
--   Differences from the source:
--   - encoding: maximum over nonnegative integer histograms ρ, σ of total n → ⨆ over ρ, σ : Fin q → Fin (n+1) with entry sum n; reason: the same finite nonempty index set; the real ⨆ over it is the maximum
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
--   - encoding: We take n ≥ 2 (p.1) → hypothesis 2 ≤ n; reason: the paper's standing assumption
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 1.2, eq. (1.2), p.2 (PDF p.5); restated p.22 (PDF p.25)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_Qstar
import Definitions.Def_PermInvCC_Supplement_Qcc
import Definitions.Def_PermInvCC_Supplement_Mf

namespace PermInvCC

namespace Supplement

/-- **Theorem 1.2 (Quantum Characterization)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, p.2; restated p.22). For a
permutation-invariant partial function `f`, let `M(f) := max_{ρ,σ} h_{f_{ρ,σ}}^{-1}`, where a
fixed-margin restriction with at most one promised label has `h_{f_{ρ,σ}} = 1` and the maximum is
over all pairs of nonnegative integer histograms of total `n`. For constants `c_q, C_q > 0`
depending only on `q`,
`c_q M(f) ≤ Q*(f) + 1 ≤ Q(f) + 1 ≤ C_q min{n, M(f) log n}` (1.2).

**Formalization Note.** `c_q, C_q` are chosen after `q` and before `n` and `f`; `n ≥ 2` is
the paper's standing assumption (p.1). `Q` is `Qcc` (no prior entanglement), `Q*` the base
`Qstar`; `M(f)` is `Mf`. Logs are base two. All three inequalities of the chain are stated. -/
theorem theorem_1_2 (q : ℕ) (hq : 2 ≤ q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ f : PartialFn n q, IsPermInvariant f →
      c * Mf f ≤ (Qstar f : ℝ) + 1 ∧ (Qstar f : ℝ) + 1 ≤ (Qcc f : ℝ) + 1 ∧
        (Qcc f : ℝ) + 1 ≤ C * min (n : ℝ) (Mf f * Real.logb 2 n) := by sorry

end Supplement

end PermInvCC
