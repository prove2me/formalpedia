-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P15_qubit_extended_upper_optimizer
-- name    : QAlgorithms.Papers.Independent.Bridge50.P15.qubit_extended_upper_optimizer
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:27:17.43484+00:00
-- url     : https://prove2.me/theorems/25422fa1-2652-46af-89c5-842b660cde7c
-- title:
--   Extended qubit thermal-attenuator upper bound and diagonal optimizer, (28),(45),(46)
-- statement:
--   Let $1/2\le\eta\le1$ and $0\le N\le1/2$. Define the qubit thermal attenuator $\Gamma_{\eta,N}$ using the ordered energy basis and coupling (7), and define its extension $\Gamma^e_{\eta,N}$ using the bath purification $\sqrt{1-N}|00\rangle+\sqrt N|11\rangle$. For $p\in[0,1]$, put $\rho_p=\operatorname{diag}(1-p,p)$. The explicit CPTP recovery $\Psi_{1-2N}\circ\Gamma_{(1-\eta)/\eta,N}$ recovers the weak complement, where $\Psi_\mu$ preserves diagonal entries and multiplies coherences by $\mu$; consequently the extension is degradable. There exists $p_*$ attaining the maximum, and
--
--   $$Q(\Gamma_{\eta,N})\le Q_1(\Gamma^e_{\eta,N})=\max_{p\in[0,1]}J(\rho_p,\Gamma^e_{\eta,N}).$$
--
--   For every physical $\rho(p,\gamma)=\begin{pmatrix}1-p&\gamma\\\bar\gamma&p\end{pmatrix}$ with $|\gamma|^2\le p(1-p)$, its extension coherent information is unchanged by $\gamma\mapsto-\gamma$ and is at most the value at $\gamma=0$. In addition, this coherent information is concave on all input density matrices: $tJ(X)+(1-t)J(Y)\le J(tX+(1-t)Y)$ for $t\in[0,1]$. All entropies are the actual entropies of the computed four-dimensional receiver and two-dimensional complement, in bits.
--
--   This gives a one-parameter optimization for the upper bound. It includes the physical recovery endpoint $\eta=1/2$ and makes no assertion of zero extension capacity below that endpoint.
-- source:
--   Narrow Bounds for the Quantum Capacity of Thermal Attenuators, arXiv:1801.04731v5, PDF p. 5, Extended qubit thermal-attenuator upper bound and diagonal optimizer, (28),(45),(46)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P15

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology Matrix

namespace QAlgorithms.Papers.Independent.Bridge50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass IsTraceClassChannel productCoeff tensorApply rankOne)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel partialLeft partialRight isometryCoeff WeaklyDegradable GaussianDensity)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Gap48.P26
  (entropyBits PhaseInsensitive weightedPhotonExpectation thermalKernel)

open QAlgorithms.Papers.Independent.Claimed50.P35 (traceClassQuantumCapacity vacuumChannel)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Support50.P07 (qubitPhaseFlipChannel)

open QAlgorithms.Papers.Independent.Information100.P08 (qubitInput thermalChannel)

/-- PDF p.5, (28), and p.9, (45)-(46), valid optimizer regime. The phase-flip
symmetry, concavity, diagonal dominance and attainment are conclusions. Printed
'mutual information' in the explanation of (45) means coherent information.
The false zero-otherwise branch is separately deferred. -/
theorem qubit_extended_upper_optimizer (eta N : ℝ) (heta : eta ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hN : N ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    IsTraceClassChannel (qubitPhaseFlipChannel N ∘ thermalChannel (1 - (1 - eta) / eta) N) ∧
    (∀ rho : State (Fin 2),
      qubitPhaseFlipChannel N (thermalChannel (1 - (1 - eta) / eta) N
        (thermalChannel (1 - eta) N rho.coefficients)) =
      extensionComplement (qubitCoupling eta) (qubitPurification N) rho.coefficients) ∧
    WeaklyDegradable (qubitExtension eta N)
      (extensionComplement (qubitCoupling eta) (qubitPurification N)) ∧
    traceClassQuantumCapacity (thermalChannel (1 - eta) N) ≤ singleLetter (qubitExtension eta N) ∧
    (∃ p ∈ Set.Icc (0 : ℝ) 1,
      (∀ q ∈ Set.Icc (0 : ℝ) 1,
        qubitExtendedCoherent eta N (qubitInput q 0) ≤
          qubitExtendedCoherent eta N (qubitInput p 0)) ∧
      singleLetter (qubitExtension eta N) =
        ENNReal.ofReal (qubitExtendedCoherent eta N (qubitInput p 0))) ∧
    (∀ p ∈ Set.Icc (0 : ℝ) 1, ∀ gamma : ℂ, Complex.normSq gamma ≤ p * (1 - p) →
      qubitExtendedCoherent eta N (qubitInput p gamma) =
        qubitExtendedCoherent eta N (qubitInput p (-gamma)) ∧
      qubitExtendedCoherent eta N (qubitInput p gamma) ≤
        qubitExtendedCoherent eta N (qubitInput p 0)) ∧
    (∀ X Y : Matrix (Fin 2) (Fin 2) ℂ, IsDensity X → IsDensity Y →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        t * qubitExtendedCoherent eta N X + (1 - t) * qubitExtendedCoherent eta N Y ≤
          qubitExtendedCoherent eta N ((t : ℂ) • X + ((1 - t : ℝ) : ℂ) • Y)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P15

end
