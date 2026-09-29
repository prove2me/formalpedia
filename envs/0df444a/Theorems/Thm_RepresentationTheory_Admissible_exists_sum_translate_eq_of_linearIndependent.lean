-- Prove2me | Theorems.Thm_RepresentationTheory_Admissible_exists_sum_translate_eq_of_linearIndependent
-- name    : RepresentationTheory.Admissible.exists_sum_translate_eq_of_linearIndependent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/e5069cb2-ca63-5bc7-bbc3-f3c4e69d6d94
-- title:
--   Density theorem for irreducible admissible smooth function spaces
-- statement:
--   Let $G$ be a group carrying a topology (no compatibility between the two structures is assumed) and let $V$ be a $\mathbb{C}$-submodule of the space of all functions $G \to \mathbb{C}$. Four hypotheses are imposed on $V$: stability under right translation, i.e. for $W \in V$ and $h \in G$ the function $g \mapsto W(gh)$ again lies in $V$; irreducibility in the form that for every $W_0 \in V$ with $W_0 \neq 0$, every $W \in V$ lies in the $\mathbb{C}$-span of the set of right translates $g \mapsto W_0(gh)$, $h \in G$; admissibility in the form that for every open subgroup $U \le G$ there is a finite set $B$ of functions $G \to \mathbb{C}$ such that every $W \in V$ satisfying $W(gk) = W(g)$ for all $k \in U$ and all $g \in G$ lies in the span of $B$; and smoothness, i.e. every $W \in V$ is right-invariant under some open subgroup $U \le G$. Then, given $n \in \mathbb{N}$, a family $u : \mathrm{Fin}\,n \to (G \to \mathbb{C})$ with all $u_i \in V$ and linearly independent over $\mathbb{C}$, and an arbitrary family $v : \mathrm{Fin}\,n \to (G \to \mathbb{C})$ with all $v_i \in V$, there exist $m \in \mathbb{N}$, scalars $c_j \in \mathbb{C}$ and elements $x_j \in G$ ($j \in \mathrm{Fin}\,m$) such that for every $i$ the function $g \mapsto \sum_j c_j\, u_i(g x_j)$ equals $v_i$ as a function on $G$.
--
--   This is a density statement of Jacobson–Burnside type for the action of the group algebra of $G$ by right translations on a space $V$ of complex-valued functions that is irreducible, admissible and smooth in the senses made explicit above: a single element of the group algebra can be prescribed to send a given finite linearly independent family to an arbitrary target family. It is used in the Langlands–Tunnell part of the argument, to produce an element of the group algebra separating a finite family of Whittaker coefficients in a Rankin–Selberg computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RepresentationTheory_Admissible_exists_sum_translate_eq_of_linearIndependent.lean

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem RepresentationTheory.Admissible.exists_sum_translate_eq_of_linearIndependent
    (G : Type) [Group G] [TopologicalSpace G]
    (V : Submodule ℂ (G → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : G, (fun g => W (g * h)) ∈ V)
    (hirr : ∀ W₀ ∈ V, W₀ ≠ 0 → ∀ W ∈ V,
      W ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => W₀ (g * h)))
    (hadm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ B : Finset (G → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : G, W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (G → ℂ)))
    (hsm : ∀ W ∈ V, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, W (g * k) = W g)
    (n : ℕ) (u : Fin n → G → ℂ) (hu : ∀ i, u i ∈ V) (hind : LinearIndependent ℂ u)
    (v : Fin n → G → ℂ) (hv : ∀ i, v i ∈ V) :
    ∃ (m : ℕ) (c : Fin m → ℂ) (x : Fin m → G),
      ∀ i : Fin n, (fun g : G => ∑ j, c j * u i (g * x j)) = v i := by sorry
