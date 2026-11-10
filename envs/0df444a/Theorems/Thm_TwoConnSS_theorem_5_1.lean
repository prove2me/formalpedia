-- Prove2me | Theorems.Thm_TwoConnSS_theorem_5_1
-- name    : TwoConnSS.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:04.9802+00:00
-- url     : https://prove2.me/theorems/3216c469-c82d-4153-9516-b5921450298b
-- title:
--   Theorem 5.1 — a polynomial-time $(1040/833+\varepsilon)$-approximation for 2ECSS
-- statement:
--   For every fixed $\varepsilon > 0$ there is a polynomial-time algorithm that, given a 2-edge-connected simple graph $G$, returns a 2-edge-connected spanning subgraph $F \subseteq E(G)$ with
--   $$|F| \le \Big(\frac{1040}{833} + \varepsilon\Big)\, \mathrm{opt}_E(G).$$
--   In particular there is a polynomial-time $1.2485$-approximation for 2ECSS, since $1040/833 < 1.2485$.
--
--   This improves the previous best ratio $5/4 - 10^{-6}$ for the minimum 2-edge-connected spanning subgraph problem (Theorem 1.1 of the paper).
--
--   Differences from the source:
--   - reading: the two algorithms give a polynomial-time (1040/833 + ε)-approximation → there exists a polynomial-time algorithm with this ratio; reason: Algorithms A and B are defined only through their exchange lemmas, so no concrete algorithm can be named; the milestones pin their structure
--   - reading: a 1.2485-approximation when ε is sufficiently small → a second conjunct: a polynomial-time algorithm with ratio 12485/10000; reason: this is what the sentence asserts
--   - encoding: polynomial time (no machine model named) → one Mathlib `Turing.TM2ComputableInPolyTime` machine over `Fin 4`, fixed before the instance, on the encodings `encIn`/`encOut` (n in unary, then the adjacency matrix; edge lists in binary); reason: Lean needs a machine model; the input length is at least n², so polynomial in the code length is polynomial in n
--   - encoding: opt_E(G), the minimum size of a 2ECSS → a comparison with every 2ECSS `F'` of `G`; reason: avoids the junk value of an infimum; same instances
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), Theorem 5.1, p.18 (PDF p.19) = Theorem 1.1, p.1 (PDF p.2); proof p.72 (PDF p.73)

import Mathlib
import Definitions.Def_TwoConnSS_Inst
import Definitions.Def_TwoConnSS_IsTwoECSS
import Definitions.Def_TwoConnSS_encIn

namespace TwoConnSS

/-- **Theorem 5.1 (= Theorem 1.1): a polynomial-time (1040/833 + ε)-approximation for 2ECSS.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), Theorem 5.1, p.18 (restating
Theorem 1.1, p.1); proof p.72: "For every fixed ε > 0, the two algorithms give a polynomial-time
(1040/833 + ε)-approximation for 2ECSS. In particular, this gives a 1.2485-approximation when ε is
sufficiently small."

1. For every real `ε > 0` there is a function `alg`, computed by a polynomial-time Turing machine,
   such that on every instance whose graph `G` is 2-edge-connected the output `F` is a 2ECSS of `G`
   and `|F| ≤ (1040/833 + ε)·|F'|` for every 2ECSS `F'` of `G`.
2. There is such a function with ratio `1.2485 = 12485/10000`.

**Formalization Note.** "The two algorithms give" is read as the existence of one polynomial-time
algorithm (Algorithms A and B are defined only through their exchange lemmas; the milestones pin
them). The machine is Mathlib's `Turing.TM2ComputableInPolyTime` on the encodings `encIn`
(`n` in unary, then the adjacency matrix) and `encOut`; one machine per fixed `ε`, chosen before the
instance. OPT is "every feasible `F'`", never an infimum. Every simple graph on `Fin n`, of every
size, is covered; the graph on one vertex is 2EC and its only solution is empty. -/
theorem theorem_5_1 :
    (∀ ε : ℝ, 0 < ε → ∃ alg : Inst → List (ℕ × ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
      ∀ I : Inst, IsTwoEC I.graph →
        IsTwoECSS I.graph (toEdges I.n (alg I)) ∧
        ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoECSS I.graph F' →
          ((toEdges I.n (alg I)).card : ℝ) ≤ (1040 / 833 + ε) * (F'.card : ℝ)) ∧
    (∃ alg : Inst → List (ℕ × ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encIn encOut alg) ∧
      ∀ I : Inst, IsTwoEC I.graph →
        IsTwoECSS I.graph (toEdges I.n (alg I)) ∧
        ∀ F' : Finset (Sym2 (Fin I.n)), IsTwoECSS I.graph F' →
          ((toEdges I.n (alg I)).card : ℝ) ≤ (12485 / 10000 : ℝ) * (F'.card : ℝ)) := by sorry

end TwoConnSS
