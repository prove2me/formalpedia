-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P06_weakstar_closed_graph_transpose
-- name    : QAlgorithms.Papers.Independent.Next46.P06.weakstar_closed_graph_transpose
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:49:15.857977+00:00
-- url     : https://prove2.me/theorems/bfd65cef-9060-426c-ba1b-b016dd561eee
-- title:
--   Theorem A.1
-- statement:
--   Let $X,Y$ be complex Banach spaces and $T\in\mathcal L(X',Y')$. Suppose its graph is closed for the product of the weak-star topologies $\sigma(X',X)$ and $\sigma(Y',Y)$. Then $T$ is continuous for these weak-star topologies and is a Banach transpose:
--
--   $$\exists S\in\mathcal L(Y,X),\quad T=S',\qquad (T\ell)(y)=\ell(Sy).$$
--
--   Closedness is full topological closedness, including arbitrary nets, rather than only sequential closedness.
-- source:
--   On the Fundamental Principles of Unbounded Functional Calculi, arXiv:2009.04733v1, PDF p. 41, Theorem A.1

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

/-- Theorem A.1, PDF p.41: a norm-bounded map of Banach duals with a
weak-star CLOSED graph is weak-star continuous and is a Banach transpose.
Closedness is topological, not merely sequential; the weak-star topology is
sigma(X',X), represented by WeakDual. -/
theorem weakstar_closed_graph_transpose [CompleteSpace X] [CompleteSpace Y]
    (T : (X →L[ℂ] ℂ) →L[ℂ] (Y →L[ℂ] ℂ))
    (hclosed : IsClosed {p : WeakDual ℂ X × WeakDual ℂ Y |
      p.2 = StrongDual.toWeakDual (T (WeakDual.toStrongDual p.1))}) :
    Continuous (fun l : WeakDual ℂ X => StrongDual.toWeakDual (T (WeakDual.toStrongDual l))) ∧
    ∃ S : Y →L[ℂ] X, ∀ l : X →L[ℂ] ℂ, T l = l.comp S := by sorry

end QAlgorithms.Papers.Independent.Next46.P06

end
