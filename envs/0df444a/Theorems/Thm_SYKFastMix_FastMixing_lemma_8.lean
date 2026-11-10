-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_lemma_8
-- name    : SYKFastMix.FastMixing.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:30.572208+00:00
-- url     : https://prove2.me/theorems/80cd29d9-e17d-432e-8734-d65c618d66c1
-- title:
--   Lemma 8 — Jacobian closeness yields the full unfiltered gap
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   Fix an arbitrary real disorder realization and $\beta\ge0$. If $\|D\gamma(\beta/2)-I\|\le1/4$, then every operator $X$ orthogonal to $\sqrt\rho$ satisfies
--   $$\langle X,K(X)\rangle_{\rm HS}\ge\tfrac34\|X\|_2^2.$$
--   In particular,
--   $$\ker K=\operatorname{span}_{\mathbb C}\{\sqrt\rho\},\qquad\operatorname{gap}(K)\ge\tfrac34.$$
--   The norm premise applies to the actual, generally non-Hermitian Jacobian. The conclusion covers both operator parity sectors and excludes additional zero modes.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 22, Lemma 8, Eq. (4.14)

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem lemma_8 {N : ℕ} (Q : Model N) (w : Disorder N) (β : ℝ) (hβ : 0 ≤ β)
    (hjac : SYKEdge.opNorm (jacobian Q w (β/2) - 1) ≤ 1/4) :
  (∀ X, hsInner (gibbsRoot (hamiltonian Q w) β) X = 0 →
    (3/4 : ℝ) * hsSq X ≤ qform (unfilteredK Q w β) X) ∧
  KernelSpan (unfilteredK Q w β) (gibbsRoot (hamiltonian Q w) β) ∧
  HasGap (unfilteredK Q w β) (gibbsRoot (hamiltonian Q w) β) (3/4) := by sorry

end SYKFastMix.FastMixing
