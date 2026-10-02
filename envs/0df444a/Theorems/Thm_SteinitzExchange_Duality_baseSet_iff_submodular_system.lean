-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_baseSet_iff_submodular_system
-- name    : SteinitzExchange.Duality.baseSet_iff_submodular_system
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:58:00.238863+00:00
-- url     : https://prove2.me/theorems/264a5199-bff3-4999-b030-3a09c361e89e
-- title:
--   Theorem 2.1 — (B1) characterizes integer points of integral submodular/supermodular base polytopes
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be finite and nonempty. The following are equivalent:
--
--   1. $B$ satisfies (B1);
--   2. there is an integer-valued submodular $f:2^V\to\mathbb Z$ with $f(\emptyset)=0$ such that $$B=\mathbb Z^V\cap\{x\in\mathbb R^V\mid x(X)\le f(X)\ (\forall X\subseteq V),\ x(V)=f(V)\};$$
--   3. there is an integer-valued supermodular $g:2^V\to\mathbb Z$ with $g(\emptyset)=0$ such that $$B=\mathbb Z^V\cap\{x\in\mathbb R^V\mid x(X)\ge g(X)\ (\forall X\subseteq V),\ x(V)=g(V)\}.$$
--
--   Moreover, the functions $f$ and $g$ are given by $f(X)=\max\{x(X)\mid x\in B\}$ and $g(X)=\min\{x(X)\mid x\in B\}$.
--
--   This folklore result identifies finite integral base sets with the integer points of integral base polytopes; in the duality theorem it provides the supermodular function $g_1$ describing $B_1$ and the submodular function $f_2$ describing $B_2$.
--
--   **Formalization Note.** The page writes $\forall X\subset V$; it is read as all subsets $X\subseteq V$ (the paper uses $\subset$ for $\subseteq$ here, and $X=V$ is covered by the equality constraint anyway). The "Moreover" clause is stated as: every $f$ (resp. $g$) as in 2 (resp. 3) equals the max (resp. min) formula.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 277, Theorem 2.1

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Duality_SetFunction

namespace SteinitzExchange.Duality

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

end SteinitzExchange.Duality
