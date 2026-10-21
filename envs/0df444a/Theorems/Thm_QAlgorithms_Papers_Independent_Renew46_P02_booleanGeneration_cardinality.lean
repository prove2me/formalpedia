-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P02_booleanGeneration_cardinality
-- name    : QAlgorithms.Papers.Independent.Renew46.P02.booleanGeneration_cardinality
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:52:24.009639+00:00
-- url     : https://prove2.me/theorems/a5e55c1f-3b17-45d8-ba7b-76ed16a2420d
-- title:
--   Lemma 9.1: Cardinality of Boolean generation
-- statement:
--   For a Boolean algebra $B$, say that $G\subseteq B$ completely generates $B$ when every order-closed Boolean subalgebra containing $G$ is all of $B$; the identity is included for free. If a finite $G$ completely generates $B$, then $B$ is finite. Moreover, if $B$ is complete and has infinite Maharam type, meaning that no finite subset completely generates it, then every completely generating $G$ has ordinary Boolean closure $B_G$ satisfying
--
--   $$
--   B_G\text{ completely generates }B,\qquad \#B_G=\#G.
--   $$
--
--   The ordinary closure uses finite Boolean operations, whereas order-closed subalgebras contain arbitrary ambient suprema. Both conclusions of the lemma are retained.
-- source:
--   Abelian von Neumann algebras, measure algebras and L^\infty-spaces, arXiv:2108.06406v2, PDF p. 45, Lemma 9.1

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02

noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

namespace QAlgorithms.Papers.Independent.Renew46.P02

universe u v

/-- Lemma 9.1, PDF pp.45--46. Finite generation is treated for arbitrary B;
the infinite-type clause also retains the exact cardinality equality. -/
theorem booleanGeneration_cardinality (B : Type u) [BooleanAlgebra B] :
    (∀ G : Set B, G.Finite → CompletelyGenerates G → Finite B) ∧
    (HasAllSuprema B → HasInfiniteMaharamType B →
      ∀ G : Set B, CompletelyGenerates G →
        CompletelyGenerates (BooleanSubalgebra.closure G : Set B) ∧
          Cardinal.mk (BooleanSubalgebra.closure G) = Cardinal.mk G) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P02

end
