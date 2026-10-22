-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_marginalEntropyAsymptotic
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.marginalEntropyAsymptotic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:10:28.104129+00:00
-- url     : https://prove2.me/theorems/b6eb2b51-9718-4ed8-a49e-3f565f847e91
-- title:
--   Proposition 4: asymptotic continuity of marginal entropy
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   For $n\ge1$, the $n$-copy energy is the additive Hamiltonian $H^{(n)}=\sum_{t=1}^n H_t$, and $S_{nM}$ means $\operatorname{Tr}(\rho H^{(n)})<nM$. Copies are regrouped as $A^n:B^n$. Finite local support of a pure state means finite Schmidt rank, without an energy-basis cutoff.
--
--   Let $\sigma\in S_M$ be pure with finite Schmidt rank. Let $\rho_n$ be arbitrary states in $S_{nM}$ satisfying $\|\rho_n-\sigma^{\otimes n}\|_1\to0$. All entropies below are finite, and
--
--   $$\lim_{n\to\infty}\frac{|E(\sigma^{\otimes n})-E(\rho_n)|}{n}=0.$$
--
--   This is continuity per copy; approximants may be mixed and have infinite support.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 6, Proposition 4: asymptotic continuity of marginal entropy

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

/-- Proposition 4, PDF pp.6--8, (15)--(16): finite LOCAL support of the limiting
pure state; arbitrary mixed approximants. Copy count is k+1; the energy is additive.
Neither (24) nor the malformed free-energy identity is a hypothesis. -/
theorem marginalEntropyAsymptotic (h : HamiltonianData) (M : ℝ) (hM : 0 < M)
    (sigma : PureState (ℕ × ℕ)) (hsigma : sigma.val ∈ energyBound h M)
    (hfinite : FiniteSchmidtRank sigma)
    (rho : (k : ℕ) → State ((Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ)))
    (henergy : ∀ k, copyMeanEnergy h (k + 1) (rho k) <
      (((k + 1 : ℕ) : ℝ) * M : EReal))
    (hlim : Tendsto (fun k => traceSize ((rho k).coefficients -
      bipartitePower sigma.val.coefficients (k + 1))) atTop (𝓝 (0 : ℝ≥0∞))) :
    (∀ k, marginalEntropy (bipartitePower sigma.val.coefficients (k + 1)) < ⊤ ∧
      marginalEntropy (rho k).coefficients < ⊤) ∧
    Tendsto (fun k => |(marginalEntropy (bipartitePower sigma.val.coefficients (k + 1))).toReal -
      (marginalEntropy (rho k).coefficients).toReal| / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
