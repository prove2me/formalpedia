-- Prove2me | Theorems.Thm_SteinerAPX_Supplement_theorem_2
-- name    : SteinerAPX.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:13:05.187185+00:00
-- url     : https://prove2.me/theorems/6416a9d8-72c5-489c-a0a3-2e605f608d8c
-- title:
--   Theorem 2 — no PTAS in $O(\log\log n)$ dimensions unless $\mathrm{NP}\subseteq\mathrm{SUBEXP}$
-- statement:
--   There are constants $C>0$ and $\beta>0$ with the following property. Call an instance a set of $n \ge 3$ distinct rational points in $\mathbb R^k$ with
--   $$k \le C \cdot \log\log n .$$
--
--   1. If some polynomial-time algorithm outputs, on every such instance, a network of segments that connects all the points and has length at most $(1+\beta)\,\mathrm{OPT}$, then $\mathrm{NP} \subseteq \mathrm{SUBEXP}$.
--   2. If some polynomial-time algorithm outputs, on every such instance, a rational $v$ with $\mathrm{OPT} \le v \le (1+\beta)\,\mathrm{OPT}$, then $\mathrm{NP} \subseteq \mathrm{SUBEXP}$.
--
--   Here $\mathrm{OPT}$ is the length of a shortest Euclidean Steiner tree of the points. In particular, unless $\mathrm{NP} \subseteq \mathrm{SUBEXP}$, Euclidean Steiner Tree has no PTAS in $O(\log\log n)$ dimensions. Arora's scheme is a PTAS in up to $\log\log n/\log\log\log n$ dimensions, so the dimension bound is tight up to a $\log\log\log n$ factor.
--
--   **Formalization Note** Instances, $\mathrm{OPT}$, polynomial time and NP are those of the published Theorem 1 (`SteinerAPX.theorem_1`); the classes of algorithms are `NetworkApproximationLogLog` and `ValueApproximationLogLog`, and SUBEXP is `InSUBEXP`.
--
--   Differences from the source:
--   - reading: "in O(log log n) dimensions" → one constant C > 0, chosen before the algorithm, with k ≤ C · ln ln n; reason: the usual meaning of O(·) in a hardness statement, and ∀ C would be false (Arora's scheme is a PTAS for small C, p.2).
--   - generalization: "admits no PTAS" (an approximation of every ratio 1 + β′) → for one fixed β > 0, a single (1 + β)-approximation already implies NP ⊆ SUBEXP; reason: a PTAS contains a (1 + β)-approximation, so the Lean statement implies the page's.
--   - generalization: point sets in O(log log n) dimensions → n ≥ 3 pairwise distinct rational points; reason: the algorithm is required to be correct on fewer instances, so more algorithms are ruled out, and a PTAS on all point sets restricts to one on these; n ≥ 3 makes log log n positive.
--   - reading: SUBEXP (not defined in the paper) → ⋂_{ε>0} DTIME(c · 2^{n^ε}) on Turing machines with finite alphabets; reason: the standard class, as used in App. A.3.
--   - encoding: algorithms, inputs and outputs → the base mission's polynomial-time TM2 machines with finite alphabets, rational coordinates in binary, the published `CookLevin.InNP`; reason: Lean convention of the published Theorem 1.
-- source:
--   Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…3fcfa9), Theorem 2, p.2 (PDF p.4); proof, §5.3, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_SteinerAPX_Supplement_InSUBEXP
import Definitions.Def_SteinerAPX_Supplement_NetworkApproximationLogLog

set_option autoImplicit false

namespace SteinerAPX.Supplement

/-- **Theorem 2 (no PTAS in `O(log log n)` dimensions unless NP ⊆ SUBEXP).** S. Bartlmae,
*Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256
6f78a9ea…), Theorem 2, p.2 (PDF p.4): "Unless NP ⊆ SUBEXP, Euclidean Steiner Tree admits no PTAS in
O(log log n) dimensions." Proof, §5.3, p.23 (PDF p.25).

There are constants `C > 0` and `β > 0` such that: if a polynomial-time algorithm outputs, on every
set of `n ≥ 3` distinct rational points in `ℝᵏ` with `k ≤ C · log log n`, a spanning network of
length at most `(1 + β) · OPT`, then NP ⊆ SUBEXP; and if a polynomial-time algorithm outputs a
rational `v` with `OPT ≤ v ≤ (1 + β) · OPT` on every such point set, then NP ⊆ SUBEXP.

**Formalization Note** "O(log log n) dimensions" is one constant `C`, chosen before the
algorithm (for small `C` Arora's scheme is a PTAS, p.2). The statement for one ratio `1 + β`
implies the absence of a PTAS (an approximation of every ratio `1 + β'`, `β' > 0`) unless
NP ⊆ SUBEXP. Instances, `OPT`, machines and NP are those of the published Theorem 1. -/
theorem theorem_2 :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧
      (NetworkApproximationLogLog C β → NPSubsetSUBEXP) ∧
      (ValueApproximationLogLog C β → NPSubsetSUBEXP) := by sorry

end SteinerAPX.Supplement
