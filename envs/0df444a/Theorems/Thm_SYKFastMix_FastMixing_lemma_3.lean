-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_3
-- name    : SYKFastMix.FastMixing.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:03.405092+00:00
-- url     : https://prove2.me/theorems/5cda03c2-b8e1-4745-9817-a8a5a45e1b90
-- title:
--   Lemma 3 — filtered gap transfers to the actual sampler
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   Fix an arbitrary real disorder realization and $\beta\ge0$. Suppose $a>0$ and
--   $$\langle X,K_f(X)\rangle_{\rm HS}\ge a\|X\|_2^2\quad\text{whenever }\langle\sqrt\rho,X\rangle_{\rm HS}=0.$$
--   Then
--   $$\operatorname{gap}(\mathcal L)\ge2a.$$
--   The conclusion includes self-adjointness and nonnegativity of the discriminant, its stationary root, and the bound on the entire orthogonal complement. This is a transfer lemma only; the main theorem assumes no gap premise.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 15, Lemma 3, Eqs. (3.24)–(3.25)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_3 {N : ℕ} (Q : Model N) (w : Disorder N) (β a : ℝ) (hβ : 0 ≤ β) (ha : 0 < a)
    (hform : ∀ X, hsInner (gibbsRoot (hamiltonian Q w) β) X = 0 →
      a * hsSq X ≤ qform (filteredK Q w β) X) :
  HasGap (discriminant (hamiltonian Q w) Q.γ β) (gibbsRoot (hamiltonian Q w) β) (2*a) := by sorry

end SYKFastMix.FastMixing
