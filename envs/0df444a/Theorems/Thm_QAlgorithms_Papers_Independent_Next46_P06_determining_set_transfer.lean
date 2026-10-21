-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_determining_set_transfer
-- name    : QAlgorithms.Papers.Independent.Next46.P06.determining_set_transfer
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-20T13:35:49.167571+00:00
-- url     : https://prove2.me/theorems/63c8f693-52a3-4c4d-9bc8-efe3993aa00f
-- title:
--   Proposition 4.4
-- statement:
--   Let $\Phi:F\to\mathcal C(X)$ be a proto-calculus, $f\in F$, and $M,E\subseteq\operatorname{bdd}(F,\Phi)$. Assume $M$ determines $\Phi$ at $f$. Define the left multiplier set
--
--   $$ B=\{h\in F:hE\subseteq\operatorname{bdd}(F,\Phi)\}.$$
--
--   Then $E$ determines $\Phi$ at $f$ if either $M$ is anchored in $E$, or for every $g\in M$ there exists a $\Phi$-anchor $N_g$ with $N_g g\subseteq BE$. Here $AB=\{ab:a\in A,b\in B\}$, and all algebras are complex and unital and $X$ is Banach. The two conditions are alternative sufficient criteria, with $B$ constructed from $E$.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 9, Proposition 4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter

open scoped Topology

namespace QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore)

universe u v w

variable {F G : Type*} [Ring F] [Algebra ℂ F] [Ring G] [Algebra ℂ G]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Proposition 4.4, PDF p.9: both alternatives, with B constructed as the
left multiplier set of E. -/
theorem determining_set_transfer [CompleteSpace X] (Phi : F → Graph X) (hPhi : Proto Phi)
    (f : F) (M E : Set F) (hM : M ⊆ boundedElements Phi)
    (hE : E ⊆ boundedElements Phi) (hdet : Determines Phi M f)
    (hcriterion : AnchoredSet Phi E M ∨
      ∀ g ∈ M, ∃ N : Set F, AnchorSet Phi N ∧
        setProduct N {g} ⊆ setProduct (leftMultipliers Phi E) E) :
    Determines Phi E f := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
