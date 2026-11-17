-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_1_3
-- name    : PermInvCC.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:01:06.99962+00:00
-- url     : https://prove2.me/theorems/5262502e-0f3f-4447-8339-69e9156fc843
-- title:
--   Theorem 1.3 — growing alphabets and graph invariance: $Q=O_\varepsilon(\log v)$, $R^{\mathrm{pub}}=\Omega_\varepsilon(v^{1-\varepsilon})$ or $\Omega_\varepsilon(v^{2-\varepsilon})$
-- statement:
--   Fix $\varepsilon \in (0,1)$. There are constants depending only on $\varepsilon$ such that each of the following holds for infinitely many sizes.
--
--   1. **Permutations.** There is a partial function $f_n : [n]^n \times [n]^n \to \{-1,+1,*\}$, invariant under simultaneous coordinate permutations, such that every promised local input contains every symbol exactly once (is a permutation of $[n]$), with
--   $$Q(f_n) = O_\varepsilon(\log n), \qquad R^{\mathrm{pub}}(f_n) = \Omega_\varepsilon(n^{1-\varepsilon}).$$
--   2. **Copies of one rigid tree.** There is a rigid tree $B$ on $[v]$ of maximum degree three and a partial function $g_v$ of two labelled graphs on $[v]$, invariant under simultaneous vertex relabelling, whose promised local graphs are all labelled copies of $B$, with
--   $$Q(g_v) = O_\varepsilon(\log v), \qquad R^{\mathrm{pub}}(g_v) = \Omega_\varepsilon(v^{1-\varepsilon}).$$
--   3. **Connected graphs.** There is a partial function $\tilde g_v$ of two connected simple graphs on $[v]$, invariant under independent relabelling of the two local graphs, with
--   $$Q(\tilde g_v) = O_\varepsilon(\log v), \qquad R^{\mathrm{pub}}(\tilde g_v) = \Omega_\varepsilon(v^{2-\varepsilon}).$$
--
--   Here $Q$ is quantum communication complexity without prior entanglement and logarithms are base two. Part 1 shows that no simulation polynomial in $Q^*(f)$, $\log n$ and $\log q$ holds once the alphabet grows; parts 1 and 2 place the hardness in the relative alignment of locally fixed objects.
--
--   **Formalization Note** Each part has its own constants and its own infinite set of sizes. A local input is promised when the function value is not $*$.
--
--   Differences from the source:
--   - reading: "for infinitely many sizes" with O_ε(·), Ω_ε(·) → constants C, c > 0 chosen after ε only; for every N a size ≥ N carrying a function with Q ≤ C·log(size) and R^pub ≥ c·size^(exponent); reason: the standard reading of asymptotic bounds along an infinite family, with constants uniform over the family
--   - encoding: every promised local input contains every symbol exactly once → x and y are bijections Fin n → Fin n whenever f x y = some b; reason: a string in [n]^n contains every symbol exactly once iff it is a bijection
--   - reading: rigid tree of maximum degree three → IsRigidTreeDeg3: a tree, all degrees ≤ 3, some degree = 3, every automorphism fixes every vertex; reason: maximum degree read as the largest degree; rigidity as defined on p.2
--   - encoding: labelled graphs on v vertices, πA, labelled copy σB → SimpleGraph (Fin v), A.map π, A = σB for some σ ∈ S_v; reason: Lean representation of §5.3's conventions
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 1.3, pp.2–3 (PDF pp.5–6); parts restated p.24 (PDF p.27), p.25 (PDF p.28); (iii) via Theorem 5.4, p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PermInvCC_PartialFn
import Definitions.Def_PermInvCC_IsPermInvariant
import Definitions.Def_PermInvCC_Rpub
import Definitions.Def_PermInvCC_Supplement_Qcc
import Definitions.Def_PermInvCC_Supplement_IsSimRelabelInvariant
import Definitions.Def_PermInvCC_Supplement_IsIndepRelabelInvariant
import Definitions.Def_PermInvCC_Supplement_IsLabelledCopy
import Definitions.Def_PermInvCC_Supplement_IsRigidTreeDeg3

namespace PermInvCC

namespace Supplement

/-- **Theorem 1.3 (Growing Alphabets and Graph Invariance)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, pp.2–3; parts restated
pp.24, 25, and (iii) proved via Theorem 5.4, p.27). For every fixed `ε ∈ (0, 1)`, there are
infinitely many sizes with the following properties.
(i) A permutation-invariant partial `f_n : [n]ⁿ × [n]ⁿ → {−1, +1, ∗}` such that every promised
local input contains every symbol exactly once, with `Q(f_n) = O_ε(log n)`,
`R^pub(f_n) = Ω_ε(n^{1−ε})`.
(ii) A partial function `g_v` of two labelled graphs on `v` vertices, invariant under
simultaneous vertex relabelling, with `Q(g_v) = O_ε(log v)`, `R^pub(g_v) = Ω_ε(v^{1−ε})`; every
promised local graph is a labelled copy of one fixed rigid tree of maximum degree three.
(iii) A partial function `g̃_v` of two connected simple graphs on `v` vertices, invariant under
independent relabelling of the two local graphs, with `Q(g̃_v) = O_ε(log v)`,
`R^pub(g̃_v) = Ω_ε(v^{2−ε})`.

**Formalization Note.** "Infinitely many sizes" with `O_ε`/`Ω_ε` is read as: constants
`C, c > 0` chosen after `ε` only, and for every `N` a size `≥ N` carrying a function with
`Q ≤ C log(size)` and `R^pub ≥ c · size^{exponent}`; each part has its own constants and sizes
(the restatements quantify each part separately). "Promised" means a value other than `∗`
(`none`); "contains every symbol exactly once" is bijectivity of `x : Fin n → Fin n`. In (ii) the
tree `B` is fixed for the size `v` and every promised graph is a labelled copy `σB`. In (iii)
every promised graph is connected. `Q` is `Qcc` (no prior entanglement). Logs are base two. -/
theorem theorem_1_3 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ f : PartialFn n n, IsPermInvariant f ∧
        (∀ x y b, f x y = some b → Function.Bijective x ∧ Function.Bijective y) ∧
        (Qcc f : ℝ) ≤ C * Real.logb 2 n ∧ c * (n : ℝ) ^ (1 - ε) ≤ (Rpub f : ℝ)) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, ∃ v : ℕ, N ≤ v ∧
      ∃ B : SimpleGraph (Fin v), IsRigidTreeDeg3 B ∧
      ∃ g : SimpleGraph (Fin v) → SimpleGraph (Fin v) → Option Bool, IsSimRelabelInvariant g ∧
        (∀ A A' b, g A A' = some b → IsLabelledCopy B A ∧ IsLabelledCopy B A') ∧
        (Qcc g : ℝ) ≤ C * Real.logb 2 v ∧ c * (v : ℝ) ^ (1 - ε) ≤ (Rpub g : ℝ)) ∧
    (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, ∃ v : ℕ, N ≤ v ∧
      ∃ g : SimpleGraph (Fin v) → SimpleGraph (Fin v) → Option Bool, IsIndepRelabelInvariant g ∧
        (∀ A A' b, g A A' = some b → A.Connected ∧ A'.Connected) ∧
        (Qcc g : ℝ) ≤ C * Real.logb 2 v ∧ c * (v : ℝ) ^ (2 - ε) ≤ (Rpub g : ℝ)) := by sorry

end Supplement

end PermInvCC
