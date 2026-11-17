-- Prove2me | Theorems.Thm_QWildMatch_Supplement_theorem_9_1
-- name    : QWildMatch.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:22:35.926952+00:00
-- url     : https://prove2.me/theorems/a3ecc15b-67ef-41fc-acad-fdc2027d1251
-- title:
--   Theorem 9.1 — $\Omega(\sqrt N)$ query lower bound for exact substring matching ($\Sigma=\{0,1,\#\}$, $P=\#1\#$, $k=0$)
-- statement:
--   Let $\Sigma=\{0,1,\#\}$, $n=3N$, the pattern $P=\#1\#$ (no wildcard) and the threshold $k=0$. Let the cost table satisfy $\mu(a,a)=0$ for every $a$ and $\mu(a,b)>0$ for $a\ne b$; insertion and deletion costs are positive. There is an absolute constant $c>0$ such that every quantum text-query algorithm that, on every text $T\in\Sigma^{3N}$, outputs whether
--   $$\exists\,0\le s\le e\le n:\ \mathrm{ED}_\mu(P,T[s:e])\le 0$$
--   correctly with probability at least $2/3$ makes at least
--   $$c\sqrt N$$
--   queries, i.e. $\Omega(\sqrt N)=\Omega(\sqrt n)$.
--
--   The bound shows that the $\sqrt{n+1}$ factor of the baseline Theorem 1.1 and the $\sqrt{(n+1)(q+1)}$ of Theorem 6.5 at $q=0$ cannot be improved in general, already for exact matching of a length-three pattern.
--
--   **Formalization Note** The query model is the base mission's `QueryAlg` with `textOracle`, for any injective symbol encoding and any finite workspace; $c$ precedes every parameter.
--
--   Differences from the source:
--   - reading: a fixed pattern of length three → the pattern #1# (no wildcard); reason: the pattern of the proof; a lower bound for it is a lower bound for 'a fixed pattern of length three'
--   - reading: even … when all nonidentical substitution, insertion, and deletion costs are strictly positive → for every cost table on {0, 1, #} with μ(a, a) = 0 (and μ(⋆, b) = 0, §3) and μ(a, b) > 0 for a ≠ b; gaps are positive by CostModel; reason: the lower bound holds for each such table; the §3 equations are the standing model
--   - reading: bounded-error algorithm requires Ω(√N) = Ω(√n) queries → ∃ absolute c > 0: every algorithm whose output equals [Match(#1#, T, 0)] with probability ≥ 2/3 on every T ∈ Σ^{3N} makes Q ≥ c√N queries; reason: the usual reading of Ω and of bounded error (error ≤ 1/3)
--   - encoding: Σ = {0, 1, #} → Fin 3 with # = 2; reason: Lean representation
--   - encoding: quantum text-query algorithm → QueryAlg with the published textOracle (index Option (Fin (3N)), symbols through any injective enc : Fin 3 → (ZMod 2)^w), Boolean output map; reason: the base mission's query model
--   - generalization: workspace of the algorithm (qubits) → any finite workspace type; reason: a lower bound over a larger class of algorithms; qubit workspaces are a special case
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…1f96), Theorem 9.1, p.12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_QWildMatch_Match
import Definitions.Def_QWildMatch_textOracle

namespace QWildMatch.Supplement

open QAlgorithms QWildMatch

open Classical in
/-- Theorem 9.1 (Search lower bound for exact substring matching), Zhao, Chen, Li, Kong, Peng, Yu, Yue,
STOC 2027 submission (file sha256 9e87a9dd…), p.12: over `Σ = {0, 1, #}`, texts of length `n = 3N`, the
pattern `#1#` and `k = 0`, every bounded-error text-query algorithm for weighted substring existence makes
`Ω(√N)` queries, for every cost table whose nonidentical substitutions and gaps are strictly positive.

**Formalization Note** `Σ` is `Fin 3` with `# = 2`; the pattern is `[some 2, some 1, some 2]` (no
wildcard). The cost table satisfies the §3 equations `μ(⋆, b) = 0`, `μ(a, a) = 0` (`IsWildcardCost`) and
`μ(a, b) > 0` for `a ≠ b`; gaps are positive by `CostModel`. `Ω(√N)` is `c √N ≤ Q` with an absolute
`c > 0` before every parameter; bounded error is success probability at least `2/3` on every text of
length `3N`. The query model is the base mission's `QueryAlg` with `textOracle`, any injective encoding,
any workspace. -/
theorem theorem_9_1 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (N : ℕ) (cm : CostModel (Fin 3)), IsWildcardCost cm →
      (∀ a b : Fin 3, a ≠ b → 0 < cm.μ (some a) b) →
    ∀ (w : ℕ) (enc : Fin 3 → (Fin w → ZMod 2)), Function.Injective enc →
    ∀ (Wk : Type) [Fintype Wk] [DecidableEq Wk] (Q : ℕ)
      (A : QueryAlg (Option (Fin (3 * N))) (Fin w → ZMod 2) Wk Q)
      (out : ((Option (Fin (3 * N)) × (Fin w → ZMod 2)) × Wk) → Bool),
      (∀ T : Fin (3 * N) → Fin 3,
        2 / 3 ≤ probEvent (A.finalState (textOracle enc T))
          (fun z => (out z = true ↔ Match cm [some 2, some 1, some 2] T 0))) →
      c * √(N : ℝ) ≤ (Q : ℝ) := by sorry

end QWildMatch.Supplement
