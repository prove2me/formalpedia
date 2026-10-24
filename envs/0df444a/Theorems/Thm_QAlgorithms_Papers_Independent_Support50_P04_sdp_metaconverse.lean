-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P04_sdp_metaconverse
-- name    : QAlgorithms.Papers.Independent.Support50.P04.sdp_metaconverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:35:14.123835+00:00
-- url     : https://prove2.me/theorems/a34f2803-58a8-49a9-87d1-65b7650d05d6
-- title:
--   Positive feasible SDP metaconverse
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on finite positive-dimensional complex Hilbert spaces with fixed orthonormal bases. Write $\widehat R(n;\varepsilon)$ and $\widehat R^{\mathrm{cpp}}(n;\varepsilon)$ for the maximum unassisted and classical-post-processing assisted entanglement-transmission rates. A code has a positive integer message dimension $M$, rate $\log_2 M/n$, and squared fidelity to the normalized maximally entangled target at least $1-\varepsilon$. A cpp encoder may retain sender memory; its decoder is LOCC across that memory and the receiver outputs, with its final quantum output at the receiver and no preshared entanglement. Let $0<\varepsilon<1$. Let $J_{\mathcal N}=(\mathrm{id}\otimes\mathcal N)(|A|\Phi_A)$ be the unnormalized Choi matrix. Define $\Gamma(\rho)=\{\Lambda\succeq0:\Lambda\preceq\rho^T\otimes I_B,\ \operatorname{tr}\Lambda J_{\mathcal N}\ge1-\varepsilon\}$. Set $f(\mathcal N,\varepsilon)=\inf_{\rho\in\mathcal S(A)}\inf_{\Lambda\in\Gamma(\rho)}\sup_J\operatorname{tr}(\Lambda J)$, where the comparison Choi operators satisfy $J\succeq0$, $J^{T_A}\succeq0$, and $\operatorname{tr}_B J=I_A$. There is at least one normalized $\rho$ with a feasible test, and
--
--   $$0<f(\mathcal N,\varepsilon)\le1,\qquad\widehat R^{\mathrm{cpp}}(1;\varepsilon)\le-\log_2 f(\mathcal N,\varepsilon).$$
--
--   The positivity clause makes the logarithmic converse a genuine finite bound.
-- source:
--   Quantum Coding with Finite Resources, arXiv:1504.04617v2, PDF p. 12, Corollary 2, Eqs. (33)–(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

namespace QAlgorithms.Papers.Independent.Support50.P04

variable {A B E : Type} [Fintype A] [DecidableEq A]

variable [Fintype B] [DecidableEq B] [Fintype E] [DecidableEq E]

/-- arXiv:1504.04617v2, PDF p.12, Corollary 2, Eqs.(33)–(34).
Gamma feasibility and strict positivity are conclusions, not assumptions smuggling
in the converse. The positive logarithm argument avoids Real.log's default at zero. -/
theorem sdp_metaconverse [Nonempty A] [Nonempty B]
    (N : Superop A B) (hN : IsChannel N) (epsilon : ℝ)
    (he0 : 0 < epsilon) (he1 : epsilon < 1) :
    (∃ rho : Matrix A A ℂ, IsDensityMatrix rho ∧
      ∃ Lambda, GammaTests N epsilon rho Lambda) ∧
    0 < metaValue N epsilon ∧ metaValue N epsilon ≤ 1 ∧
    cppBoundary N 1 epsilon ≤ ((-QAlgorithms.Papers.Independent.Information100.P80.log2 (metaValue N epsilon) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Support50.P04

end
