-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_general_outer_bounds
-- name    : QAlgorithms.Papers.Independent.Support50.P04.general_outer_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:29:30.895219+00:00
-- url     : https://prove2.me/theorems/212d4eff-8b3f-4ef4-8c05-7922552f5546
-- title:
--   General SDP and covariant dispersion converse
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Let $J_{\mathcal N}=(\mathrm{id}\otimes\mathcal N)(|A|\Phi_A)$ be the unnormalized Choi matrix. Define $\Gamma(\rho)=\{\Lambda\succeq0:\Lambda\preceq\rho^T\otimes I_B,\ \operatorname{tr}\Lambda J_{\mathcal N}\ge1-\varepsilon\}$. Set $f(\mathcal N,\varepsilon)=\inf_{\rho\in\mathcal S(A)}\inf_{\Lambda\in\Gamma(\rho)}\sup_J\operatorname{tr}(\Lambda J)$, where the comparison Choi operators satisfy $J\succeq0$, $J^{T_A}\succeq0$, and $\operatorname{tr}_B J=I_A$. Fix $0<\varepsilon<1$. All logarithms are binary and $\Phi^{-1}$ is the standard Gaussian quantile. Remainder constants may depend on the fixed channel and error, and are chosen before the block length: there are $C>0$ and $n_0\ge2$ such that the displayed bound holds for every integer $n\ge n_0$. For every integer $n\ge1$, $f(\mathcal N^{\otimes n},\varepsilon)>0$ and
--
--   $$\widehat R^{\mathrm{cpp}}(n;\varepsilon)\le-\frac1n\log_2 f(\mathcal N^{\otimes n},\varepsilon).$$
--
--   Let $\omega=(\mathrm{id}\otimes\mathcal N)(\Phi_A)$. The Rains set is $\mathrm{PPT}^{\prime}=\{\sigma\succeq0:\|\sigma^{T_B}\|_1\le1\}$. Put $I_R(\mathcal N)=\min_{\sigma\in\mathrm{PPT}^{\prime}}D(\omega\|\sigma)$, where $D$ is Umegaki relative entropy in bits, infinite on support failure. Let $\Pi_R$ be its full minimizer set and let $V_R^{\varepsilon}$ be the maximum of the relative-information variance $V(\omega\|\sigma)$ over $\Pi_R$ if $\varepsilon<1/2$, and the minimum otherwise. If $\mathcal N$ is covariant for the full input unitary group with an output unitary representation, then $I_R$ is finite and
--
--   $$\widehat R^{\mathrm{cpp}}(n;\varepsilon)\le I_R(\mathcal N)+\sqrt{V_R^\varepsilon(\mathcal N)/n}\,\Phi^{-1}(\varepsilon)+C\log_2n/n.$$
--
--   Both clauses are converse bounds.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 7, Result 4, Eqs. (13)–(14)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF pp.7,11–13, Result 4, Eqs.(13)–(14).
Printed (13) omits 1/n; changed to per-use normalization as Eq.(1) and Eq.(39)
require. Covariance is the full-unitary convention explicitly stated on p.12. -/
theorem general_outer_bounds [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    (∀ n : ℕ, 0 < n → 0 < metaValue (piSuperop (fun _ : Fin n => N)) epsilon ∧
      cppBoundary N n epsilon ≤ ((-QAlgorithms.Papers.Independent.Information100.P80.log2 (metaValue (piSuperop (fun _ : Fin n => N)) epsilon) / n : ℝ) : EReal)) ∧
    (FullUnitaryCovariant N →
      ∃ a : ℝ, rainsInformation N = (a : EReal) ∧
        dispersionUpper (fun n => cppBoundary N n epsilon) a (rainsVariance N epsilon) epsilon) := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
