-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_4
-- name    : SYKFastMix.FastMixing.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:07.306314+00:00
-- url     : https://prove2.me/theorems/17a289f9-0c56-468f-ab23-885b381a7a4d
-- title:
--   Lemma 4 — exact commutator identity for jump differences
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   Fix an arbitrary real disorder realization and $\beta\ge0$. For $c_i(X)=(\widetilde\gamma_iX-X\widetilde\gamma_i^\dagger)/2$, every operator $X$ and every site $i$ satisfy
--   $$c_i([H,X])-[H,c_i(X)]=\sum_j M(\widetilde\gamma,\widetilde\gamma^\dagger)_{ij}(c_j(X)).$$
--   The block operator is exactly (2.13), including the signs and factor $1/3$. This algebraic identity controls evolution of the unfiltered jump differences and has no probabilistic qualification.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 17, Lemma 4, Eq. (3.40)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_4 {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (X : Mat (SiteHilbert N)) (i : Fin N) :
  applySuper (cMap Q w β i) (hamiltonian Q w * X - X * hamiltonian Q w) -
    (hamiltonian Q w * applySuper (cMap Q w β i) X - applySuper (cMap Q w β i) X * hamiltonian Q w) =
  ∑ j, applySuper
    (mBlock w (imaginary Q w (β/4)) (imaginary Q w (-(β/4)))
      (imaginary Q w (β/4)) (imaginary Q w (-(β/4))) i j)
    (applySuper (cMap Q w β j) X) := by sorry

end SYKFastMix.FastMixing
