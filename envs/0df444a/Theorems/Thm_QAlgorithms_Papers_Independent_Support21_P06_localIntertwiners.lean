-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P06_localIntertwiners
-- name    : QAlgorithms.Papers.Independent.Support21.P06.localIntertwiners
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:37:34.214532+00:00
-- url     : https://prove2.me/theorems/5188c6df-412a-4a22-82dd-060bcd1d5385
-- title:
--   Local intertwiners on generalized weight spaces
-- statement:
--   Let $n\ge1$ and let $q\in\mathbb C^\times$ be not a root of unity. Let $M$ be a finite-dimensional complex module for the affine Hecke algebra with commuting invertible generators $x_1,\ldots,x_n$, quadratic relations $T_i^2=(q-q^{-1})T_i+1$, and the braid and mixed relations of §1. For a weight $t=(t_1,\ldots,t_n)\in(\mathbb C^\times)^n$, put
--   $$
--   M_t^{\mathrm{gen}}=\{m:\ \text{for every }j,\ (x_j-t_j)^{k_j}m=0\text{ for some }k_j>0\}.
--   $$
--   Fix $1\le i<n$ with $t_i\ne t_{i+1}$. The operator $x_{i+1}-x_i$ is invertible on this generalized weight space, and
--   $$
--   \tau_i=T_i-(q-q^{-1})x_{i+1}(x_{i+1}-x_i)^{-1}
--   $$
--   maps $M_t^{\mathrm{gen}}$ into $M_{s_it}^{\mathrm{gen}}$, where $s_i$ exchanges coordinates $i$ and $i+1$. On $M_t^{\mathrm{gen}}$ one has
--   $$
--   x_i\tau_i=\tau_i x_{i+1},\qquad x_{i+1}\tau_i=\tau_i x_i,\qquad x_j\tau_i=\tau_i x_j\quad(j\ne i,i+1),
--   $$
--   $$
--   \tau_i^2=\frac{(qx_{i+1}-q^{-1}x_i)(qx_i-q^{-1}x_{i+1})}{(x_{i+1}-x_i)(x_i-x_{i+1})}.
--   $$
--   For valid generator indices, the local operators also satisfy
--   $$
--   \tau_i\tau_j=\tau_j\tau_i\quad(|i-j|>1),\qquad
--   \tau_i\tau_{i+1}\tau_i=\tau_{i+1}\tau_i\tau_{i+1}\quad(1\le i<n-1),
--   $$
--   whenever both sides are defined. Each factor is evaluated on the weight space reached by the factors to its right; it is defined precisely when the corresponding adjacent weight coordinates differ.
--
--   These identities provide the local intertwiners used to compare weight spaces.
--
--   **Formalization Note** The module is encoded by generating complex linear endomorphisms satisfying exactly the affine Hecke relations. Fractions are explicit finite geometric-series inverses on the generalized weight space, with both inverse laws included in the conclusion; no inverse in the Laurent polynomial algebra is asserted. Lean indices are zero-based.
-- source:
--   Skew shape representations are irreducible, arXiv:math/0401326v2, PDF p. 8, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P06

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent nextPosition)

attribute [local instance] Classical.propDecidable

/-- Proposition 3.2, both parts and all operator identities (PDF pp.8–9).
The inverse laws pin down the endomorphism interpretation of every fraction.
Braid indices are valid adjacent generator pairs, correcting the printed upper
bound; all compositions retain the continuation "whenever both sides are well
defined". No pairwise-distinctness restriction is imposed on the weight. -/
theorem localIntertwiners
    (n : ℕ) (hn : 0 < n) (q : ℂ) (hq : GenericParameter q)
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : AffineAction n q V) (t : Fin n → ℂ) (ht : TorusWeight t)
    (i : Adjacent n) (hi : t i.val ≠ t (nextPosition i)) :
    (∀ m, IsGeneralizedWeightVector A t m →
      (A.x (nextPosition i) - A.x i.val)
        (differenceInverse A t i.val (nextPosition i) m) = m ∧
      differenceInverse A t i.val (nextPosition i)
        ((A.x (nextPosition i) - A.x i.val) m) = m ∧
      IsGeneralizedWeightVector A (permuteWeight (simplePerm i) t)
        (tauGeneralized A t i m) ∧
      A.x i.val (tauGeneralized A t i m) =
        tauGeneralized A t i (A.x (nextPosition i) m) ∧
      A.x (nextPosition i) (tauGeneralized A t i m) =
        tauGeneralized A t i (A.x i.val m) ∧
      (∀ j, j ≠ i.val → j ≠ nextPosition i →
        A.x j (tauGeneralized A t i m) = tauGeneralized A t i (A.x j m)) ∧
      tauGeneralized A (permuteWeight (simplePerm i) t) i (tauGeneralized A t i m) =
        (((q • A.x (nextPosition i) - q⁻¹ • A.x i.val) *
          (q • A.x i.val - q⁻¹ • A.x (nextPosition i))) *
          differenceInverse A t i.val (nextPosition i) *
          differenceInverse A t (nextPosition i) i.val) m) ∧
    (∀ j : Adjacent n,
      (i.val.val + 1 < j.val.val ∨ j.val.val + 1 < i.val.val) →
      WordDefined [i, j] t → WordDefined [j, i] t →
      ∀ m, IsGeneralizedWeightVector A t m →
        tauGeneralizedWord A [i, j] t m = tauGeneralizedWord A [j, i] t m) ∧
    (∀ j : Adjacent n, j.val.val = i.val.val + 1 →
      WordDefined [i, j, i] t → WordDefined [j, i, j] t →
      ∀ m, IsGeneralizedWeightVector A t m →
        tauGeneralizedWord A [i, j, i] t m = tauGeneralizedWord A [j, i, j] t m) := by sorry

end QAlgorithms.Papers.Independent.Support21.P06

end
