-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_proposition_B_2
-- name    : SurgeSpatial.Attraction.proposition_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:44.508997+00:00
-- url     : https://prove2.me/theorems/33171fe4-4b05-41d0-affa-e7b93fa29b48
-- title:
--   Proposition B-2, p. B-5 — pasting a local equilibrium into an attraction region
-- statement:
--   Let $(p,\mathcal T)$ be a feasible solution of (P2) and $z\in\mathcal C$ a sink, with $A=A(z\mid p,\mathcal T)$, $\Gamma(A)>0$, and $\mathcal L=\bigcup_a\{X_a(z\mid p,\mathcal T)\}$. Let $\tilde\Theta$ be the measure on $A$ of drivers that stay within $A$ under $\mathcal T$: $\tilde\Theta(B)=\mathcal T(B\times A)$ for measurable $B\subseteq A$. Suppose that
--
--   1. $\tilde p$ is a price mapping, measurable on $A$, with values in $[0,\bar V]$ on $A$;
--   2. $\tilde{\mathcal T}\in\mathcal F_A(\tilde\Theta)$ is a local equilibrium in $A$ under $\tilde p$;
--   3. $V_A(x\mid\tilde p,\tilde{\mathcal T})\le V(x\mid p,\mathcal T)$ for all $x\in A$, and $\tilde\Theta(\{x\in A:V_A(x\mid\tilde p,\tilde{\mathcal T})=V(x\mid p,\mathcal T)\})=\tilde\Theta(A)$.
--
--   Define the pasted price $\hat p=\tilde p$ on $A$ and $\hat p=p$ off $A$, and the pasted flow
--   $$\hat{\mathcal T}(B)=\mathcal T\big(B\cap((A^c\cup\mathcal L)\times A^c)\big)+\tilde{\mathcal T}\big(B\cap(A\times A)\big),$$
--   with $A^c=\mathcal C\setminus A$. Then $(\hat p,\hat{\mathcal T})$ is a feasible solution of (P2), and
--   $$s^{\hat{\mathcal T}}(x)=\begin{cases}s^{\tilde{\mathcal T}}(x)&x\in A,\\ s^{\mathcal T}(x)&x\in A^c,\end{cases}\qquad\Gamma\text{-a.e.}$$
--
--   Any local equilibrium in an attraction region that keeps drivers' utilities at or below the old ones, with equality where the staying drivers start, can be pasted into the global equilibrium.
--
--   **Formalization Note** $\tilde\Theta$ is written literally as the restriction to $A$ of $B\mapsto\mathcal T(B\times A)$. $\Gamma(A)>0$ is the precondition of Definition 3 (local equilibria are defined only for such sets). Densities of $\tilde{\mathcal T}$ are taken with respect to $\Gamma$, which agrees with $\Gamma|_A$ $\Gamma$-a.e. on $A$. The density identity is stated $\Gamma$-a.e., since densities are defined only up to null sets.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. B-5, Proposition B-2 and Definition 3

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

open scoped Classical in
theorem proposition_B_2 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (z : E) (hz : z ∈ M.C) (hsink : M.IsSink p T z)
    (hΓA : 0 < M.Γ (M.attr p T z)) (pt : E → ℝ) (Tt : Measure (E × E))
    (hpt : Measurable ((M.attr p T z).domRestrict pt))
    (hpt_range : ∀ x ∈ M.attr p T z, pt x ∈ Set.Icc 0 M.Vbar)
    (hTt : M.FeasFlowOn (M.attr p T z)
      (((T.restrict (Set.univ ×ˢ M.attr p T z)).map Prod.fst).restrict (M.attr p T z)) Tt)
    (hloc : M.IsLocalEquilibrium (M.attr p T z)
      (((T.restrict (Set.univ ×ˢ M.attr p T z)).map Prod.fst).restrict (M.attr p T z)) pt Tt)
    (hle : ∀ x ∈ M.attr p T z, M.VB (M.attr p T z) pt Tt x ≤ M.V p T x)
    (heq : (((T.restrict (Set.univ ×ˢ M.attr p T z)).map Prod.fst).restrict (M.attr p T z))
        {x | x ∈ M.attr p T z ∧ M.VB (M.attr p T z) pt Tt x = M.V p T x} =
      (((T.restrict (Set.univ ×ˢ M.attr p T z)).map Prod.fst).restrict (M.attr p T z))
        (M.attr p T z)) :
    M.FeasibleP2 ((M.attr p T z).piecewise pt p)
        (T.restrict (((M.C \ M.attr p T z) ∪ Set.range (M.Xend p T z)) ×ˢ
            (M.C \ M.attr p T z)) + Tt.restrict (M.attr p T z ×ˢ M.attr p T z)) ∧
      M.sT (T.restrict (((M.C \ M.attr p T z) ∪ Set.range (M.Xend p T z)) ×ˢ
            (M.C \ M.attr p T z)) + Tt.restrict (M.attr p T z ×ˢ M.attr p T z))
        =ᵐ[M.Γ] (M.attr p T z).piecewise (M.sT Tt) (M.sT T) := by sorry

end SurgeSpatial.Attraction
