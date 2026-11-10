-- Prove2me | Theorems.Thm_RemovingTrees_Main_improvement_step
-- name    : RemovingTrees.Main.improvement_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:11.30655+00:00
-- url     : https://prove2.me/theorems/b3bb56a6-c4ed-481a-9503-83a5b82c9615
-- title:
--   Lemma 3.7 — Efficient improvement of an (η,r,C)-subgraph
-- statement:
--   Let $k$ be a positive even integer and let $G$ be a finite undirected multigraph on at least two vertices with $\lambda(G)\ge k$. Suppose $H$ is an $(\eta,r,C)$-subgraph in Definition 3.6, so all three packing and residual-connectivity clauses hold. Assume
--   $$
--   \eta\le\frac14,\qquad88C\le\frac{k}{4},\qquad
--   \alpha=44^{\lfloor4\eta^{-2}\rfloor}\text{ divides }r.
--   $$
--   A uniform polynomial-time procedure constructs a subgraph $H'\subseteq H$ which is an $(3\eta/4,r/\alpha,C)$-subgraph, returning both the selected packing and a residual packing witness. The exact-arithmetic implementation covers every real parameter admitted by these hypotheses, and a bit implementation covers rational $\eta$ with its full binary length charged.
--
--   This is the source's improvement step, including every clause of Definition 3.6. There is no restriction $r\le C$, no equality requirement $k=\lambda(G)$, and no positive-$\eta$ restriction.
--
--   **Formalization Note** Real inversion is totalized at zero, so $\alpha(0)=1$ and $H'=H$ is allowed. The input includes witnesses for the two packings already asserted by Definition 3.6; these are not promises of a desired improved output.
--
--   Differences from the source:
--   - encoding: finite undirected multigraphs on at least two vertices → vertices Fin n with n ≥ 2 and individually labeled edges Fin m with symmetric endpoint cuts; reason: every source graph admits such labels; loops and parallel edges are retained
--   - encoding: efficient construction with real-valued data → charged finite exact-arithmetic/sign machine for all real inputs, with a separate bit implementation for rational inputs where stated; reason: retains every real input and measures bit cost on the rational data used by the paper
--   - encoding: possibly negative number of residual packed trees → integer lower bound on the length of an explicitly returned nonnegative packing; reason: avoids natural subtraction underflow and preserves the source lower bound
--   - encoding: H is an (η,r,C)-subgraph → all three defining clauses plus explicit witnesses for its two packings in the computational input; reason: these witnesses already exist by Definition 3.6; no extra graph condition is imposed and all input bits are charged
--   - generalization: η⁻² is defined only for η ≠ 0 → also η = 0 with α = 1; reason: totalized inversion adds a valid boundary case: retain H unchanged
--   - generalization: construct an improved subgraph H′ of G → the improved subgraph also satisfies H′ ⊆ H; reason: this stronger inclusion is explicitly produced in the source proof on pp.7–8
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), Lemma 3.7 and Definition 3.6, p.6; construction of H′, pp.7–8

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

set_option autoImplicit false

namespace RemovingTrees.Main

/-- Lemma 3.7, p.6; includes the proof's H′ ⊆ H and witnesses for both packings.
At η=0 the totalized inverse gives α=1; negative η is not excluded. -/
theorem improvement_step :
    ∃ R : RealMachine, ∃ B : OAI.CurrentKS.Machine, ∃ a d : ℕ, 0 < a ∧
    (∀ (n m : ℕ) (G : MultiGraph n m) (k r C : ℕ) (η : ℝ)
      (H : Finset (Fin m)) (ts us : List (Finset (Fin m))),
      2 ≤ n → 0 < k → Even k → CutLower G Finset.univ k →
      GoodSubgraph G k η r C H → ImprovementWitness G k r C H ts us →
      η ≤ (1:ℝ)/4 → (88:ℝ)*C ≤ (k:ℝ)/4 → alpha η ∣ r →
      RealResult R a d (ImprovementInput G k r C H ts us) [η]
        (ImprovementOutput G k r C η H)) ∧
    (∀ (n m : ℕ) (G : MultiGraph n m) (k r C : ℕ) (η : ℚ)
      (H : Finset (Fin m)) (ts us : List (Finset (Fin m))),
      2 ≤ n → 0 < k → Even k → CutLower G Finset.univ k →
      GoodSubgraph G k (η:ℝ) r C H → ImprovementWitness G k r C H ts us →
      (η:ℝ) ≤ (1:ℝ)/4 → (88:ℝ)*C ≤ (k:ℝ)/4 → alpha (η:ℝ) ∣ r →
      BitResult B a d (ImprovementInput G k r C H ts us ++ encRat η)
        (ImprovementOutput G k r C (η:ℝ) H)) := by sorry
end RemovingTrees.Main
