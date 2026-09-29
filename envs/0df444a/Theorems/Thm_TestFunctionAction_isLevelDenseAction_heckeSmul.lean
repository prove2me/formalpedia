-- Prove2me | Theorems.Thm_TestFunctionAction_isLevelDenseAction_heckeSmul
-- name    : TestFunctionAction.isLevelDenseAction_heckeSmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/0aa74a19-8d22-5c18-9cfc-d071ec0565bc
-- title:
--   Level-wise density of the test-function action
-- statement:
--   Let $G$ be a Hausdorff topological group equipped with a measurable space structure that is the Borel structure of its topology, let $V$ be a complex vector space, and let $\pi : G \to \operatorname{End}_{\mathbb C}(V)$ be a group homomorphism into the multiplicative monoid of $\mathbb C$-linear endomorphisms of $V$. Assume: `hsm`, that $\pi$ is smooth in the sense that for every $v \in V$ the stabiliser subgroup $\{g \in G : \pi(g)v = v\}$ is open; $\mu$ is a Haar measure on $G$; `hirr`, that $V$ contains a nonzero vector and every submodule $W \subseteq V$ with $\pi(g)W \subseteq W$ for all $g$ equals $\bot$ or $\top$; and `hadm`, that for every subgroup $K \le G$ whose underlying set is compact and open the space of $K$-fixed vectors $\{v : \pi(u)v = v \text{ for all } u \in K\}$ is finite-dimensional over $\mathbb C$. The conclusion is that the $\mathbb C$-linear map `heckeSmulHom π hsm μ` from the Schwartz–Bruhat test space of $G$ (the submodule of $\varphi : G \to \mathbb C$ satisfying `IsSchwartzBruhat`, acting by $v \mapsto \int \varphi(g)\,\pi(g)v$ in the finite-range sense of `heckeSmul`) to $\operatorname{End}_{\mathbb C}(V)$ is a level-dense action: for every compact open subgroup $K \le G$, every $\mathbb C$-linear functional $\ell : V \to \mathbb C$ with $\ell(\pi(k)x) = \ell(x)$ for all $k \in K$ and $x \in V$, and every $x_0 \in V$ with $\pi(k)x_0 = x_0$ for all $k \in K$, there exists a test function $\varphi$ with `heckeSmulHom π hsm μ` $\varphi$ acting as $x \mapsto \ell(x) \cdot x_0$ on all of $V$.
--
--   This is the standard density statement for the action of the Hecke algebra of locally constant compactly supported functions on a smooth irreducible admissible representation: at each level $K$ the rank-one operators $x \mapsto \ell(x)x_0$ built from a $K$-invariant functional and a $K$-fixed vector are already realised by test functions, the archetypal consequence being a Burnside-type surjectivity onto the endomorphisms of the finite-dimensional space of $K$-fixed vectors. It feeds the Whittaker multiplicity-one argument used in the cubic-induction step of the Langlands–Tunnell input, via [`LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace`](thm.html#LanglandsTunnell.CubicInduction.hasWhittakerMultOne_of_ne_one_of_forall_mem_gl3CyclicSubspace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TestFunctionAction_isLevelDenseAction_heckeSmul.lean

import Definitions.Def_RepTheory_LevelDensity
import Definitions.Def_RepTheory_TestFunctionActionHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open FLT.SmoothAdmissibleSchurCommutant SchwartzBruhatSpace TestFunctionAction

theorem TestFunctionAction.isLevelDenseAction_heckeSmul
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π)
    (μ : Measure G) [μ.IsHaarMeasure]
    (hirr : IsIrreducibleRep π) (hadm : IsAdmissibleRep π) :
    TwistedPairing.IsLevelDenseAction π (heckeSmulHom π hsm μ) := by sorry
