-- Prove2me | Theorems.Thm_SYKFastMix_FastMixing_theorem_1
-- name    : SYKFastMix.FastMixing.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:08:09.653335+00:00
-- url     : https://prove2.me/theorems/e5a7e1d8-3d97-4f84-a3cd-c07513204019
-- title:
--   Theorem 1 — constant-gap, worst-case Gibbs mixing for SYK
-- statement:
--   Let $N\ge4$ be even, $J>0$, $d=2^{N/2}$, and let $\gamma_1,\ldots,\gamma_N$ be any Hermitian CAR family on $\mathbb C^d$. The couplings are independent $\mathcal N(0,6J^2/N^3)$ variables and $H=\sum_{|A|=4}J_A\gamma_A$, using raw ordered quartic products. All traces are unnormalized and all operator norms are induced by Euclidean or Hilbert–Schmidt norms.
--
--   There is a measurable disorder event of probability at least $1-2e^{-N}$ on which, simultaneously for every real $0\le\beta\le1/(1000J)$, the actual Gibbs sampler of (2.20) has
--   $$\operatorname{gap}(\mathcal L)\ge\frac{507}{392}>1.$$
--   For every real $0<\epsilon<1$ its worst-case trace-norm mixing time satisfies
--   $$t_{\rm mix}(\epsilon)\le\frac{392}{507}\left(\frac N4\log2+2\beta JN+\log\frac1\epsilon\right).$$
--   The paper writes $O(N+\log(1/\epsilon))$; its proof yields precisely this prefactor and bracket in (5.38), with gap constant $507/392$ in (5.37). All density matrices, including coherences between parity sectors, enter the mixing-time definition. No good-disorder, Jacobian, stationarity, or gap assumption is supplied to the theorem.
--
--   Differences from the source:
--   - encoding: one-based sites on a complex Hilbert space with unnormalized traces → zero-based finite matrix coordinates, full operator spaces, and real parts of Hermitian quadratic forms; reason: an orthonormal basis identifies every source representation with these matrices; real parts do not change the real quadratic forms
--   - generalization: for each inverse temperature the probability is at least 1-2 exp(-N) → one event works simultaneously for every allowed inverse temperature; reason: the event in Corollary 15 and the proof on p.28 are uniform over all those temperatures
--   - encoding: a system-size-independent gap and O(N + log(1/epsilon)) mixing time → gap 507/392 and the exact mixing inequality (5.38), with an ENNReal infimum; reason: these are the paper’s own explicit proof constants, with no weakened rate or restricted error parameter
-- source:
--   Yiyi Cai, Yongtao Zhan, Alexander Zlokapa, Fast mixing of the SYK model at high temperatures, STOC 2027 submission #1050 (October 2026), p. 2, Theorem 1; explicit proof constants in Eqs. (5.37)–(5.38), p.28

import Mathlib
import Definitions.Def_SYKFastMix_FastMixing_Coefficients
import Definitions.Def_SYKFastMix_FastMixing_CompactGaussian

noncomputable section
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexOrder

namespace SYKFastMix.FastMixing

theorem theorem_1 {N : ℕ} (Q : Model N) :
  ∃ A : Set (Disorder N), MeasurableSet A ∧
    ENNReal.ofReal (1 - 2 * Real.exp (-(N : ℝ))) ≤ disorderLaw Q A ∧
    ∀ w ∈ A, ∀ β : ℝ, 0 ≤ β → β ≤ 1 / (1000 * Q.J) →
      HasGap (discriminant (hamiltonian Q w) Q.γ β) (gibbsRoot (hamiltonian Q w) β) (507/392) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        mixingTime (lindblad (hamiltonian Q w) Q.γ β) (gibbs (hamiltonian Q w) β) ε ≤
          ENNReal.ofReal ((392/507 : ℝ) * ((N : ℝ)/4 * Real.log 2 +
            2 * β * Q.J * N + Real.log (1/ε))) := by sorry

end SYKFastMix.FastMixing
