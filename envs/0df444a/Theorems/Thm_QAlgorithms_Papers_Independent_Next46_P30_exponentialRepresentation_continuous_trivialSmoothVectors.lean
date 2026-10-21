-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P30_exponentialRepresentation_continuous_trivialSmoothVectors
-- name    : QAlgorithms.Papers.Independent.Next46.P30.exponentialRepresentation_continuous_trivialSmoothVectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:18:54.266203+00:00
-- url     : https://prove2.me/theorems/d6608f76-49bc-4d75-962b-947f4a393d5d
-- title:
--   The phase representation is continuous and has only the zero smooth vector
-- statement:
--   Let $G=L^2([0,1],\mathbb R)$ be the additive real Hilbert space and let $H=L^2([0,1],\mathbb C)$ be the complex Hilbert space, both for Lebesgue measure and with their norm topologies. Elements are equivalence classes modulo equality almost everywhere. Define the particular action $\pi(f)\xi=e^{if}\xi$, with multiplication interpreted almost everywhere.
--
--   A vector $\xi\in H$ is smooth when its orbit map $G\to H$, $f\mapsto\pi(f)\xi$, is $C^n$ over the reals for every natural number $n$. Write $H^\infty$ for the set of all such vectors. Then
--
--   $$
--   ((f,\xi)\mapsto\pi(f)\xi)\text{ is jointly continuous on }G\times H,\qquad H^\infty=\{0\}.
--   $$
--
--   This gives a continuous unitary representation of a real Banach–Lie group whose smooth-vector space is trivial. No normalization is imposed on the Hilbert vectors.
-- source:
--   A non-smooth continuous unitary representation of a Banach-Lie group, arXiv:0811.4234v1, PDF p. 4, Theorem 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P30

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Next46.P30

/-- Theorem 2.3 (arXiv:0811.4234v1, PDF p. 4): the specific phase representation
is jointly continuous and its complete smooth-vector set is exactly the singleton {0}. -/
theorem exponentialRepresentation_continuous_trivialSmoothVectors :
    Continuous (fun z : GroupSpace × HilbertSpace => phaseAction z.1 z.2) ∧
      smoothVectors = ({0} : Set HilbertSpace) := by sorry

end QAlgorithms.Papers.Independent.Next46.P30

end
