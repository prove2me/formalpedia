-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_rains_dispersion_converse
-- name    : QAlgorithms.Papers.Independent.Support50.P04.rains_dispersion_converse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:37:52.46125+00:00
-- url     : https://prove2.me/theorems/ce61b45b-ddc7-43a9-9237-23f3d4a76c00
-- title:
--   Rains-information dispersion converse
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Fix $0<\varepsilon<1$. All logarithms are binary and $\Phi^{-1}$ is the standard Gaussian quantile. Remainder constants may depend on the fixed channel and error, and are chosen before the block length: there are $C>0$ and $n_0\ge2$ such that the displayed bound holds for every integer $n\ge n_0$. Let $\omega=(\mathrm{id}\otimes\mathcal N)(\Phi_A)$. The Rains set is $\mathrm{PPT}^{\prime}=\{\sigma\succeq0:\|\sigma^{T_B}\|_1\le1\}$. Put $I_R(\mathcal N)=\min_{\sigma\in\mathrm{PPT}^{\prime}}D(\omega\|\sigma)$, where $D$ is Umegaki relative entropy in bits, infinite on support failure. Let $\Pi_R$ be its full minimizer set and let $V_R^{\varepsilon}$ be the maximum of the relative-information variance $V(\omega\|\sigma)$ over $\Pi_R$ if $\varepsilon<1/2$, and the minimum otherwise. Assume full input-unitary covariance, with an output unitary representation. The Rains information is finite and
--
--   $$\widehat R^{\mathrm{cpp}}(n;\varepsilon)\le I_R(\mathcal N)+\sqrt{V_R^\varepsilon(\mathcal N)/n}\,\Phi^{-1}(\varepsilon)+C\log_2n/n.$$
--
--   This supplies a channel-dependent outer bound.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 13, Theorem 3, Eqs. (41)–(43)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.13, Theorem 3, Eqs.(41)–(43).
All Rains minimizers are constructed from N; maximum variance is chosen below 1/2,
minimum at/above 1/2. Constants may depend on fixed N and epsilon. -/
theorem rains_dispersion_converse [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (hcov : FullUnitaryCovariant N)
    (epsilon : ℝ) (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    ∃ a : ℝ, rainsInformation N = (a : EReal) ∧
      dispersionUpper (fun n => cppBoundary N n epsilon) a (rainsVariance N epsilon) epsilon := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
