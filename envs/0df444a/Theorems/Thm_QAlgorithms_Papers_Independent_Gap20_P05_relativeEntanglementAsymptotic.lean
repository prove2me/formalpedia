-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P05_relativeEntanglementAsymptotic
-- name    : QAlgorithms.Papers.Independent.Gap20.P05.relativeEntanglementAsymptotic
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:16:31.128602+00:00
-- url     : https://prove2.me/theorems/038c341e-7afc-456c-b85b-fa91f90c17de
-- title:
--   Proposition 9: asymptotic continuity of relative entropy of entanglement
-- statement:
--   Both local systems have the full infinite-dimensional separable complex Hilbert space $\ell^2(\mathbb N)$, and the joint system is their completed Hilbert tensor product. A state is a positive trace-class operator of trace one. The norm $\|X\|_1=\operatorname{Tr}|X|$ is the full trace norm. Entropy $S$ is extended von Neumann entropy in bits, with $0\log_2 0=0$, and $E(\rho)=S(\operatorname{Tr}_B\rho)$.
--
--   The local Hamiltonians have complete orthonormal eigenbases and real eigenvalues $e_A(i),e_B(j)$ indexed with multiplicity in nondecreasing order. The joint Hamiltonian is $H=H_A\otimes I+I\otimes H_B$, with $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Its finite ground energy need not be nonnegative. For $M>0$, write $S_M=\{\rho:\operatorname{Tr}(\rho H)<M\}$.
--
--   For each comparison set $C\in\{D,P\}$, let $E_R^C(\rho)=\inf_{\tau\in C}D_2(\rho\|\tau)$, where $D_2$ is the extended quantum relative entropy in bits, $D$ is the trace-norm closed convex hull of product states, and $P$ is the trace-norm closure of states whose partial transpose is a state. The comparison states have no energy constraint.
--
--   For $n\ge1$, the $n$-copy energy is the additive Hamiltonian $H^{(n)}=\sum_{t=1}^n H_t$, and $S_{nM}$ means $\operatorname{Tr}(\rho H^{(n)})<nM$. Copies are regrouped as $A^n:B^n$. Finite local support of a pure state means finite Schmidt rank, without an energy-basis cutoff.
--
--   Let $\sigma\in S_M$ be pure with finite Schmidt rank, and let arbitrary states $\rho_n\in S_{nM}$ satisfy $\|\rho_n-\sigma^{\otimes n}\|_1\to0$. For each $C\in\{D,P\}$ the displayed values are finite and
--
--   $$\lim_{n\to\infty}\frac{|E_R^C(\sigma^{\otimes n})-E_R^C(\rho_n)|}{n}=0.$$
--
--   This is relative-entropy entanglement continuity per copy for both comparison classes.
-- source:
--   On the quantification of entanglement in infinite-dimensional quantum systems, arXiv:quant-ph/0112064v3, PDF p. 12, Proposition 9: asymptotic continuity of relative entropy of entanglement

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

/-- Proposition 9, PDF pp.12--13, (51): relative-entropy asymptotic continuity,
for each of D and P, at pure finite-Schmidt-rank tensor powers. No existence of
an optimizer or bounded logarithm of a Gibbs state is assumed. -/
theorem relativeEntanglementAsymptotic (h : HamiltonianData) (M : ℝ) (hM : 0 < M)
    (sigma : PureState (ℕ × ℕ)) (hsigma : sigma.val ∈ energyBound h M)
    (hfinite : FiniteSchmidtRank sigma)
    (rho : (k : ℕ) → State ((Fin (k + 1) → ℕ) × (Fin (k + 1) → ℕ)))
    (henergy : ∀ k, copyMeanEnergy h (k + 1) (rho k) <
      (((k + 1 : ℕ) : ℝ) * M : EReal))
    (hlim : Tendsto (fun k => traceSize ((rho k).coefficients -
      bipartitePower sigma.val.coefficients (k + 1))) atTop (𝓝 (0 : ℝ≥0∞))) :
    ∀ ppt : Bool,
      (∀ k, comparisonRelativeEntropyBits ppt (bipartitePower sigma.val.coefficients (k + 1)) < ⊤ ∧
        comparisonRelativeEntropyBits ppt (rho k).coefficients < ⊤) ∧
      Tendsto (fun k => |(comparisonRelativeEntropyBits ppt (bipartitePower sigma.val.coefficients (k + 1))).toReal -
        (comparisonRelativeEntropyBits ppt (rho k).coefficients).toReal| / ((k + 1 : ℕ) : ℝ))
        atTop (𝓝 (0 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P05

end
