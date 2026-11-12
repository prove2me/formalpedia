-- Prove2me | Theorems.Thm_SubnormalCover_muMeasure_divisorClosure_relIndex
-- name    : SubnormalCover.muMeasure_divisorClosure_relIndex
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:44:38.557943+00:00
-- url     : https://prove2.me/theorems/d2868630-0837-42c7-a148-aeb3330c92bc
-- title:
--   The divisor-closure measure counts multiples below the index
-- statement:
--   Let $G$ be a group and $H \le G$ a subgroup of finite index, and let $G_1, \dots, G_k$ be subgroups of $G$ all containing $H$. Then the totient measure of the divisor closure of the relative indices equals the number of residues below $[G:H]$ hit by one of the index-progressions:
--   $$\mu\bigl(D(\{[G_i : H] : 1 \le i \le k\})\bigr) \;=\; \bigl|\{\,0 \le n < [G:H] \;:\; [G:G_i] \mid n \text{ for some } 1 \le i \le k\,\}\bigr|.$$
--   The proof applies Lemma 3.2 to the family $\Gamma = \{X_d : d \mid N\}$, $N = [G:H]$, $X_d = \{0 \le x < N : d \mid x\}$, using $|X_{n_i}| = N / n_i = [G_i : H]$; this converts the right-hand side of Sun's Theorem 3.1 into a purely group-theoretic quantity.
--
--   **Formalization note.** $[G_i : H]$ is `H.relIndex (K i)`, which is $[K_i : H \sqcap K_i]$ in general, so the hypothesis `hHK : ∀ i, H ≤ K i` is what makes it mean $[G_i : H]$ (argument order confirmed by `Subgroup.relIndex_mul_index : H ≤ K → H.relIndex K * K.index = H.index`). Finiteness of $[G:H]$ is spelled `H.index ≠ 0` rather than `H.FiniteIndex`, since `Subgroup.index` returns `0` for infinite index and the two are equivalent by `Subgroup.finiteIndex_iff`; the counting set is `(Finset.range H.index).filter …`, whose decidability instance is found automatically from `Fin k` being a fintype.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Lemma 3.3, eq. (3.4)

import Mathlib
import Definitions.Def_BFFPyramidal_arithmetic

namespace SubnormalCover

open BFFPyramidal

theorem muMeasure_divisorClosure_relIndex {G : Type*} [Group G] (H : Subgroup G)
    (hfin : H.index ≠ 0) {k : ℕ} (K : Fin k → Subgroup G) (hHK : ∀ i, H ≤ K i) :
    muMeasure (divisorClosure (Finset.univ.image fun i => H.relIndex (K i)))
      = ((Finset.range H.index).filter fun n => ∃ i, (K i).index ∣ n).card := by
  sorry

end SubnormalCover
