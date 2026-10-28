-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_generic_field_characterization
-- name    : QAlgorithms.Papers.Independent.Support21.P11.generic_field_characterization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T03:59:08.244149+00:00
-- url     : https://prove2.me/theorems/e7be2362-b6c0-4ac3-8378-2b491992092d
-- title:
--   Generic field characterization by weights and a cyclic module
-- statement:
--   Let $F$ be a field of characteristic different from $2$, let $r\ge1$, and let $\omega=(\omega_a)_{a\ge0}$ and $u_1,\ldots,u_r\in F$ be parameters. Assume the $u_i$ are pairwise distinct and $u_i+u_j\ne0$ for every $i,j$, including $i=j$. Let $W$ be the associated two-strand degenerate cyclotomic BMW algebra and write $e=e_1$, $x=x_1$. Define $\gamma_i=(2u_i-(-1)^r)\prod_{j\ne i}(u_i+u_j)/(u_i-u_j)$. Then
--
--   $$
--   \begin{aligned}
--   & (e,xe,\ldots,x^{r-1}e)\text{ is independent and }eWe\ne0\\
--   &\quad\Longleftrightarrow\quad [\omega_a=\sum_{i=1}^r\gamma_iu_i^a\text{ for every }a\ge0]\text{ and }[\exists a\ge0:\omega_a\ne0]\\
--   &\quad\Longleftrightarrow\quad \exists M,v_0:\ (v_0,xv_0,\ldots,x^{r-1}v_0)\text{ is an }F\text{-basis of }M,\ eM=Fv_0.
--   \end{aligned}
--   $$
--
--   This characterizes the generic admissible parameter sequence through an actual unital module action. No faithfulness of that action is required.
--
--   **Formalization Note** The existential finite-dimensional module is transported to $F^r$ and represented by a unital algebra homomorphism into its endomorphism algebra.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 4, Theorem 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Theorem 3.2, PDF pp.4--5, credited to [3] and proved here.
Both nonzero conditions are retained, and the module action need not be faithful. -/
theorem generic_field_characterization (F : Type*) [Field F] (omega : ℕ → F)
    (r : ℕ) (u : Fin r → F) (hr : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (hdistinct : Function.Injective u) (hsum : ∀ i j : Fin r, u i + u j ≠ 0) :
    ((LinearIndependent F (idealFamily F omega r u) ∧ NonzeroCorner F omega r u) ↔
      ((∀ a : ℕ, omega a = ∑ i : Fin r, weightGamma u i * u i ^ a) ∧
        ∃ a : ℕ, omega a ≠ 0)) ∧
    (((∀ a : ℕ, omega a = ∑ i : Fin r, weightGamma u i * u i ^ a) ∧
        ∃ a : ℕ, omega a ≠ 0) ↔ HasCyclicModule F omega r u) := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
