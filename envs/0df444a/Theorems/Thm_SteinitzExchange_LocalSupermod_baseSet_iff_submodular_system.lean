-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_baseSet_iff_submodular_system
-- name    : SteinitzExchange.LocalSupermod.baseSet_iff_submodular_system
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:49:07.297977+00:00
-- url     : https://prove2.me/theorems/edb77a52-144b-43f9-8c25-a478f5203d07
-- title:
--   Theorem 2.1 — base sets are the integer points of integral submodular/supermodular systems
-- statement:
--   Let $V$ be a finite nonempty set and $B\subseteq\mathbb Z^V$ a finite nonempty set. The following are equivalent:
--
--   1. $B$ satisfies the exchange axiom (B1);
--   2. there is an integer-valued submodular $f:2^V\to\mathbb Z$ with $f(\emptyset)=0$ such that $B=\{x\in\mathbb Z^V\mid x(X)\le f(X)\ \forall X\subseteq V,\ x(V)=f(V)\}$;
--   3. there is an integer-valued supermodular $g:2^V\to\mathbb Z$ with $g(\emptyset)=0$ such that $B=\{x\in\mathbb Z^V\mid x(X)\ge g(X)\ \forall X\subseteq V,\ x(V)=g(V)\}$.
--
--   Moreover, any $f$ as in 2 and any $g$ as in 3 are given by
--
--   $$f(X)=\max\{x(X)\mid x\in B\},\qquad g(X)=\min\{x(X)\mid x\in B\}\qquad(X\subseteq V).$$
--
--   This folklore theorem identifies finite integral base sets with the integer points of integral base polytopes; the supermodular function $g$ is the function $X\mapsto\psi^\circ(\chi_X)$ appearing in condition (C1).
--
--   **Formalization Note.** The paper writes "$\forall X\subset V$"; this is read as all $X\subseteq V$ (the constraint at $X=V$ is implied by the equality). The paper intersects $\mathbb Z^V$ with a polyhedron in $\mathbb R^V$; for integer $x$ and integer $f$ the real inequalities coincide with the integer ones, so the sets are described in $\mathbb Z^V$ directly. "Moreover" is stated in its strong reading: every $f$ (resp. $g$) satisfying 2 (resp. 3) equals the displayed max (resp. min) function; together with 1 ⇒ 2 this shows that the displayed functions work under (B1).
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 277, Theorem 2.1

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Matroidal

namespace SteinitzExchange.LocalSupermod

/-- Murota 1996, p. 277, Theorem 2.1. For a finite nonempty `B ⊆ ℤ^V`:
(a) (B1) ⇔ (b) `B = {x ∈ ℤ^V | x(X) ≤ f(X) ∀ X ⊆ V, x(V) = f(V)}` for an integer-valued
submodular `f` with `f(∅) = 0`; (a) ⇔ (c) the same with a supermodular `g` and `≥`.
Moreover any such `f` is `X ↦ max{x(X) | x ∈ B}` and any such `g` is `X ↦ min{x(X) | x ∈ B}`.
The page's "∀X ⊂ V" is read as all `X ⊆ V`. -/
theorem baseSet_iff_submodular_system {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hne : B.Nonempty) :
    (IsIntegralBaseSet B ↔
      ∃ f : Finset V → ℤ, IsSubmodular f ∧ f ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) ∧
    (IsIntegralBaseSet B ↔
      ∃ g : Finset V → ℤ, IsSupermodular g ∧ g ∅ = 0 ∧
        ∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) ∧
    (∀ f : Finset V → ℤ, IsSubmodular f → f ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, sumOn x X ≤ f X) ∧ sumOn x Finset.univ = f Finset.univ) →
      ∀ X : Finset V, f X = B.sup' hne (fun x => sumOn x X)) ∧
    (∀ g : Finset V → ℤ, IsSupermodular g → g ∅ = 0 →
      (∀ x : V → ℤ, x ∈ B ↔
          (∀ X : Finset V, g X ≤ sumOn x X) ∧ sumOn x Finset.univ = g Finset.univ) →
      ∀ X : Finset V, g X = B.inf' hne (fun x => sumOn x X)) := by sorry

end SteinitzExchange.LocalSupermod
