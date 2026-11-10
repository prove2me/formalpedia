-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_7
-- name    : SYKFastMix.FastMixing.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:18.516828+00:00
-- url     : https://prove2.me/theorems/4c3dab5e-d7d5-45f5-9dd3-a1826361042a
-- title:
--   Lemma 7 — Clifford identities and the entire common kernel
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   Fix an arbitrary real disorder realization and $\beta\ge0$. Set $\widetilde\gamma_i=\gamma_i(\beta/4)$ and $b_i(X)=(\widetilde\gamma_iX-P(X)\widetilde\gamma_i^\dagger)/2$. With Hilbert–Schmidt adjoints of these superoperators,
--   $$\{b_i,b_j\}=0,\qquad \{b_i,b_j^\dagger\}(X)=\tfrac14\left(\{\widetilde\gamma_i,\widetilde\gamma_j^\dagger\}X+X\{\widetilde\gamma_j,\widetilde\gamma_i^\dagger\}\right).$$
--   Moreover,
--   $$\bigcap_i\ker b_i=\operatorname{span}_{\mathbb C}\{\sqrt\rho\}.$$
--   All operators, including odd ones, are included. Both identities and the exact common kernel are needed for the unfiltered gap estimate.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 21, Lemma 7, Eqs. (4.5)–(4.7), statement continues p.22

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_7 {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β) :
  (∀ i j, bMap Q w β i * bMap Q w β j + bMap Q w β j * bMap Q w β i = 0) ∧
  (∀ i j X, applySuper (bMap Q w β i * (bMap Q w β j)ᴴ + (bMap Q w β j)ᴴ * bMap Q w β i) X =
    (1 / 4 : ℂ) •
      (anticomm (imaginary Q w (β/4) i) ((imaginary Q w (β/4) j)ᴴ) * X +
       X * anticomm (imaginary Q w (β/4) j) ((imaginary Q w (β/4) i)ᴴ))) ∧
  (∀ X, (∀ i, applySuper (bMap Q w β i) X = 0) ↔
    ∃ z : ℂ, X = z • gibbsRoot (hamiltonian Q w) β) := by sorry

end SYKFastMix.FastMixing
