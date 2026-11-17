-- Prove2me | Theorems.Thm_PermInvCC_Supplement_theorem_5_4
-- name    : PermInvCC.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:00:13.915195+00:00
-- url     : https://prove2.me/theorems/7278daa0-eb39-4a13-b551-1b63b13ea004
-- title:
--   Theorem 5.4 — encoding communication problems by graphs on $\Theta(\sqrt m)$ vertices, preserving $R^{\mathrm{pub}}$, $Q$, $Q^*$
-- statement:
--   There are absolute constants $c_1, c_2 > 0$ such that for every $m \ge 1$ there are $v$ with $c_1\sqrt m \le v \le c_2\sqrt m$ and an encoding of $m$-bit strings as graphs on $[v]$,
--
--   $$x \mapsto \mathrm{enc}(x), \qquad \mathrm{enc}(x) \text{ connected}, \qquad \mathrm{enc}(x) \cong \mathrm{enc}(x') \iff x = x',$$
--
--   with the following property: for every partial communication function $F : \{0,1\}^m \times \{0,1\}^m \to \{-1,+1,*\}$, the induced graph function $\widetilde F$ (value $F(x,y)$ on a labelled copy of $\mathrm{enc}(x)$ against a labelled copy of $\mathrm{enc}(y)$, and $*$ otherwise) is invariant under independent relabelling and
--
--   $$C(\widetilde F) = C(F), \qquad C \in \{R^{\mathrm{pub}}, Q, Q^*\}. \tag{5.10}$$
--
--   Consequently, for every $\varepsilon \in (0,1)$ there are constants $C, c > 0$ depending only on $\varepsilon$ and infinitely many $v$ carrying such an induced graph function with
--
--   $$Q(\widetilde F) \le C\log v, \qquad R^{\mathrm{pub}}(\widetilde F) \ge c\,v^{2-\varepsilon}. \tag{5.11}$$
--
--   Here $Q$ is quantum communication complexity without prior entanglement, $Q^*$ the entanglement-assisted one, and logarithms are base two. The encoding stores $\Theta(v^2)$ bits in the isomorphism type of a connected graph on $v$ vertices and yields Theorem 1.3(iii).
--
--   **Formalization Note** In (5.11) the graph function is again induced by an encoding with connected, pairwise non-isomorphic graphs.
--
--   Differences from the source:
--   - generalization: every F_m has a complexity-preserving embedding (∀ F ∃ embedding) → one encoding, depending on m only, works for every F (∃ enc ∀ F); reason: the paper's construction depends on m only; ∃ enc ∀ F implies ∀ F ∃ enc
--   - reading: complexity-preserving embedding into connected simple graphs → enc with every enc x connected, enc x ≅ enc x' ↔ x = x', and F̃ = graphEmbed enc F (labelled copies of enc x against enc y get F x y, else ∗); reason: the embedding of the proof (p.27), stated by its defining properties
--   - reading: v = Θ(√m) → absolute c₁, c₂ > 0 with c₁√m ≤ v ≤ c₂√m for every m ≥ 1; reason: Θ with absolute constants
--   - reading: (5.11) "infinitely many v" with O_ε(·), Ω_ε(·) → constants C, c > 0 chosen after ε only; for every N a size ≥ N carrying a function with Q ≤ C·log(size) and R^pub ≥ c·size^(exponent); reason: the standard reading of asymptotic bounds along an infinite family, with constants uniform over the family
--   - reading: explicit graph functions F̃_v → graphEmbed enc F for some F and some connected, injective-up-to-isomorphism enc; reason: "explicit" has no formal content
--   - encoding: R^pub, Q and Q* of Definition 2.1 (Bob outputs) → base Rpub (transcript-determined output), base Qstar (EntQProtocol) and Qcc (EntQProtocol with the all-zero start state); reason: the base mission's model conventions; requiring both parties to output changes costs by at most one bit (p.9)
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 5.4, eqs. (5.10)–(5.11), p.26 (PDF p.29); construction p.27 (PDF p.30)

import Mathlib
import Definitions.Def_PermInvCC_Rpub
import Definitions.Def_PermInvCC_Qstar
import Definitions.Def_PermInvCC_Supplement_Qcc
import Definitions.Def_PermInvCC_Supplement_IsIndepRelabelInvariant
import Definitions.Def_PermInvCC_Supplement_graphEmbed

namespace PermInvCC

namespace Supplement

/-- **Theorem 5.4 (Encoding Communication Problems by Graphs)** (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, p.26). Every partial
communication function `F_m` with `m ≥ 1` input bits on each side has a complexity-preserving
embedding into connected simple graphs on `v = Θ(√m)` vertices. The resulting partial function
`F̃_v` is invariant under independent relabelling, and `C(F̃_v) = C(F_m)` for
`C ∈ {R^pub, Q, Q*}` (5.10). Consequently, for every fixed `ε ∈ (0, 1)` there are infinitely
many `v` and explicit graph functions satisfying `Q(F̃_v) = O_ε(log v)`,
`R^pub(F̃_v) = Ω_ε(v^{2−ε})` (5.11).

**Formalization Note.** An embedding is an encoding `enc` of `m`-bit strings as graphs on `[v]`
such that every `enc x` is connected and encodings of distinct strings are non-isomorphic; `F̃` is
`graphEmbed enc F` (a labelled copy of `enc x` against one of `enc y` gets `F x y`, anything else
`∗`). `v = Θ(√m)` is read with absolute `c₁, c₂ > 0`. The encoding depends on `m` only and is
chosen before `F` (as in the proof), which implies the per-`F` statement. In (5.11) the graph
function is again `graphEmbed enc F` for such an encoding; constants `C, c` are chosen after `ε`
only. "Explicit" has no formal content. `Q` is `Qcc`; logs are base two. -/
theorem theorem_5_4 :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ m : ℕ, 1 ≤ m →
      ∃ v : ℕ, ∃ enc : (Fin m → Bool) → SimpleGraph (Fin v),
        c₁ * Real.sqrt m ≤ v ∧ (v : ℝ) ≤ c₂ * Real.sqrt m ∧
        (∀ x, (enc x).Connected) ∧ (∀ x x', Nonempty (enc x ≃g enc x') ↔ x = x') ∧
        ∀ F : (Fin m → Bool) → (Fin m → Bool) → Option Bool,
          IsIndepRelabelInvariant (graphEmbed enc F) ∧
          Rpub (graphEmbed enc F) = Rpub F ∧ Qcc (graphEmbed enc F) = Qcc F ∧
          Qstar (graphEmbed enc F) = Qstar F) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, ∃ v : ℕ, N ≤ v ∧
      ∃ m : ℕ, ∃ enc : (Fin m → Bool) → SimpleGraph (Fin v),
        (∀ x, (enc x).Connected) ∧ (∀ x x', Nonempty (enc x ≃g enc x') ↔ x = x') ∧
        ∃ F : (Fin m → Bool) → (Fin m → Bool) → Option Bool,
          IsIndepRelabelInvariant (graphEmbed enc F) ∧
          (Qcc (graphEmbed enc F) : ℝ) ≤ C * Real.logb 2 v ∧
          c * (v : ℝ) ^ (2 - ε) ≤ (Rpub (graphEmbed enc F) : ℝ)) := by sorry

end Supplement

end PermInvCC
