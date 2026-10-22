-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_exampleOne
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.exampleOne
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T23:06:27.440538+00:00
-- url     : https://prove2.me/theorems/9734ea3c-3439-4087-9122-50adb2096e0d
-- title:
--   Example 1: discontinuity at the product ground state
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   Let $\psi_0=|0\rangle_A|0\rangle_B$, and for integers $k\ge2$ put $\delta_k=1/\log_2 k$ and
--
--   $$\psi_k=\sqrt{1-\delta_k}\,\psi_0+\sqrt{\delta_k/k}\sum_{j=1}^k|j\rangle_A|j\rangle_B,\qquad \sigma_k=|\psi_k\rangle\langle\psi_k|.$$
--
--   These vectors are normalized, and
--
--   $$\lim_{k\to\infty}\|\sigma_k-|\psi_0\rangle\langle\psi_0|\|_1=0,\qquad \lim_{k\to\infty}E(\sigma_k)=1,\qquad E(|\psi_0\rangle\langle\psi_0|)=0.$$
--
--   This explicit sequence exhibits discontinuity of marginal entropy at a product state. No uniform energy bound is imposed. The printed index $k=1$ is excluded because its delta is undefined; the logarithm base is fixed by the asserted one-bit limit.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 3, Example 1: discontinuity at the product ground state

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P05

noncomputable section

open Filter

open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Gap20.P05

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (generalizedRelativeEntropy traceSecond)

open QAlgorithms.Entanglement (partialTransposeFirst)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartitePower)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)

/-- Example 1, PDF p.3, (4)--(5). Printed: k starts at 1 and delta=1/log k.
Changed: use k+2 and log base two, because the printed first term is undefined
and the asserted entropy limit is one bit. The sequence is the displayed vector,
not an arbitrary convergent family; no uniform energy bound is imposed. -/
theorem exampleOne (_h : HamiltonianData) :
    (∀ k : ℕ, ‖exampleVector (k + 2)‖ = 1) ∧
    Tendsto (fun k : ℕ => traceSize
      (rankOne (exampleVector (k + 2)) - rankOne (lp.single 2 (0, 0) (1 : ℂ))))
      atTop (𝓝 (0 : ℝ≥0∞)) ∧
    Tendsto (fun k : ℕ => marginalEntropy (rankOne (exampleVector (k + 2))))
      atTop (𝓝 (1 : ℝ≥0∞)) ∧
    marginalEntropy (rankOne (lp.single 2 (0, 0) (1 : ℂ))) = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
