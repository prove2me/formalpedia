-- Prove2me | Theorems.Thm_STCSublinear1377_Main_lemma_3_2
-- name    : STCSublinear1377.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:58.901409+00:00
-- url     : https://prove2.me/theorems/638b8e58-6a68-444b-9901-7e5ca867d70b
-- title:
--   Lemma 3.2 — All four laminar-family guarantees
-- statement:
--   Let $G$ be any connected simple unweighted graph of order $n\ge2$, let $k=\operatorname{STC}(G)$ and take $D\ge4k$. Algorithm 1 has a polynomial-time implementation receiving only $G$ and the threshold and returning its named laminar family $\mathcal L$. With one absolute constant $C$, its conclusions are
--
--   $$\operatorname{depth}(\mathcal L)\le C\log(|H|+2),\qquad H=\{v:d_G(v)>D\},$$
--
--   $$G[S]\text{ is connected},\quad b_G(S)\le D\quad(S\in\mathcal L),$$
--
--   $$\left|\left(S\setminus\bigcup_{A\in\mathcal L,A\subsetneq S}A\right)\cap H\right|\le1\quad(S\in\mathcal L),\qquad V_G\in\mathcal L.$$
--
--   Laminarity is also asserted explicitly. These are conclusions, not conditions imposed on a family supplied to the algorithm. The local implementation may choose any disjoint connected exact minimum isolating sets; the structural conclusions hold for every resulting execution.
--
--   **Formalization Note** Degrees and cut weights on these integer-weighted graphs are integers. The machine therefore receives the binary encoding of $\lfloor D\rfloor$, while the statement and execution relation retain every real threshold $D\ge4k$.
--
--   Differences from the source:
--   - encoding: an arbitrary finite graph → a binary adjacency table on Fin n; reason: every finite graph can be enumerated, and symmetry and absence of loops are checked explicitly
--   - generalization: Lemma 3.2 asserts only that LaminarConstruction constructs the family (its running time is argued separately, p.7 IsolatingSets and p.15) → in addition, one uniform finite-work-alphabet TM2 evaluator with a polynomial step bound outputs an encoding of the family of a successful execution; reason: the extra clause implies the source statement, and the source's own running-time remarks support it
--   - encoding: a real degree threshold D → the evaluator receives floor D, while comparisons in the execution relation use D; reason: all current degrees and boundaries are integers, so floor D makes exactly the same comparisons
--   - generalization: the family returned by IsolatingSets in Algorithm 1 → the same four guarantees for every execution using disjoint connected minimum isolating sets; reason: the proof uses only the exact isolating-set properties and applies to every permitted subroutine choice
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, Algorithm 1 and Lemma 3.2, PDF/printed p.8; continuation p.9

import Definitions.Def_STCSublinear1377_Main_DataMachine
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- Algorithm 1 is realized by a finite-alphabet polynomial-time machine; no oracle or supplied
family is an input. The four conclusions are uniform over every legal choice of isolating cuts. -/
theorem lemma_3_2 :
    ∃ a : BinaryEvaluator, ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n → ∀ g : Table n, isInput g → ∀ d : ℝ,
        4 * (stc g : ℝ) ≤ d →
        (∃ l : NamedFamily n,
          LaminarExecution (original g) (d : ℝ) (some l) ∧
          encodesFamily (a.eval (graphTapeBits g [] ++ natBits (Int.toNat ⌊d⌋))) l) ∧
        (∀ l : NamedFamily n, LaminarExecution (original g) (d : ℝ) (some l) →
          laminar l ∧
          (familyDepth l : ℝ) ≤ C * Real.log ((hubs (original g) d).card + 2 : ℝ) ∧
          (∀ s ∈ regions l, (original g).connectedSet s ∧ (original g).boundary s ≤ d) ∧
          (∀ s ∈ regions l, ((residual l s) ∩ hubs (original g) d).card ≤ 1) ∧
          (Finset.univ : Finset (Fin n)) ∈ regions l) := by sorry

end STCSublinear1377.Main
