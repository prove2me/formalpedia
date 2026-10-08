-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_components_tfae
-- name    : WhitneyMatroid.Components.components_tfae
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:50:30.163478+00:00
-- url     : https://prove2.me/theorems/5c07e838-abfb-447b-a5f2-42913a7cc719
-- title:
--   Theorem 18 — three characterizations of the components
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$ with rank function $r$, and let $M_1,\dots,M_p$ be distinct, nonempty, non-separable subsets of $E$ with $M_1+\cdots+M_p=E$. Then the following statements are equivalent:
--
--   1. $M_1,\dots,M_p$ are the components of $M$ (the set $\{M_1,\dots,M_p\}$ is the set of components);
--   2. no two of $M_1,\dots,M_p$ have common elements, and there is no circuit of $M$ containing elements of more than one of them;
--   3. $$
--   r(E) = r(M_1)+\cdots+r(M_p).
--   $$
--
--   The theorem shows that the components are detected by rank additivity alone, and that they are separated from each other by circuits.
--
--   **Formalization Note** Whitney tacitly takes $M_1,\dots,M_p$ to be distinct, nonempty matroids. Both are made explicit: if two of them could coincide, a single loop $e$ listed twice ($M_1=M_2=\{e\}$) would satisfy (3) but not (2); if one could be empty, (2) and (3) would hold but (1) would fail. The family is indexed by $\mathrm{Fin}\,p$; ranks are Mathlib's `M.eRk`, finite here. As Whitney remarks, rank cannot be replaced by nullity in (3).
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 520, Theorem 18

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable
import Definitions.Def_WhitneyMatroid_Components_IsComponent

namespace WhitneyMatroid.Components

theorem components_tfae {α : Type*} (M : Matroid α) [M.Finite]
    (p : ℕ) (Ms : Fin p → Set α) (hcover : (⋃ i, Ms i) = M.E)
    (hinj : Function.Injective Ms) (hne : ∀ i, (Ms i).Nonempty)
    (hns : ∀ i, IsNonSeparable M (Ms i)) :
    [Set.range Ms = {K : Set α | IsComponent M K},
     (∀ i j, i ≠ j → Disjoint (Ms i) (Ms j)) ∧
       ¬ ∃ (P : Set α) (i j : Fin p), i ≠ j ∧ M.IsCircuit P ∧
         (P ∩ Ms i).Nonempty ∧ (P ∩ Ms j).Nonempty,
     M.eRk M.E = ∑ i, M.eRk (Ms i)].TFAE := by sorry

end WhitneyMatroid.Components
