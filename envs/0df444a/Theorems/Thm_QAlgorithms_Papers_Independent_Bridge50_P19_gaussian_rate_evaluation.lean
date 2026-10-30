-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P19_gaussian_rate_evaluation
-- name    : QAlgorithms.Papers.Independent.Bridge50.P19.gaussian_rate_evaluation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:55:54.475325+00:00
-- url     : https://prove2.me/theorems/54a7066d-8afb-4fdb-8467-f260259d87e6
-- title:
--   Actual broadcast CVQKD classical entropies and adversarial Holevo information
-- statement:
--   Let $\eta_B,\eta_C\ge0$ with $\eta_B+\eta_C\le1$ be the transmissivities of a two-receiver vacuum pure-loss broadcast channel, and let $\mu\ge0$ be finite. Alice sends one half of a two-mode squeezed vacuum of mean photon number $\mu$, homodynes the retained mode, and publicly announces her random quadrature choice. Bob and Charlie heterodyne, retaining the corresponding sifted quadratures $Y,Z$; write $X$ for Alice's outcome. Model each retained heterodyne quadrature by trusted 50% loss followed by homodyne detection, with vacuum variance $1/2$. All quantities below are computed from these actual Born densities and measurement-conditioned quantum ensembles, in bits. Put $v=2\mu+1$ and $a=\pi e$. Then
--
--   $$\begin{aligned}
--   H(XYZ)&=\tfrac12\log_2\!\left[a^3\left(1+\left(1-\tfrac{\eta_B+\eta_C}{2}\right)(v-1)\right)\right],\\
--   H(X)&=\tfrac12\log_2(av),\\
--   H(Y)&=\tfrac12\log_2\!\left[a\left(1+\tfrac{\eta_B}{2}(v-1)\right)\right],\\
--   H(Z)&=\tfrac12\log_2\!\left[a\left(1+\tfrac{\eta_C}{2}(v-1)\right)\right],\\
--   H(XY)&=\tfrac12\log_2\!\left[a^2\left(1+\left(1-\tfrac{\eta_B}{2}\right)(v-1)\right)\right],\\
--   H(XZ)&=\tfrac12\log_2\!\left[a^2\left(1+\left(1-\tfrac{\eta_C}{2}\right)(v-1)\right)\right].
--   \end{aligned}$$
--
--   For $t=\eta_B$, let $D=CE$ be Charlie's full premeasurement output together with the channel environment; for $t=\eta_C$, let $D=BE$. Trusted detector loss is excluded from $D$. Grouping the adversarial modes leaves one active mode and a vacuum factor. Set
--
--   $$\alpha_t=1+\frac{(1-t)(v-1)}{1+t(v-1)/2},\quad \beta_t=1+(1-t)(v-1),\quad n_t=\frac{\sqrt{\alpha_t\beta_t}-1}{2}.$$
--
--   With $W=Y$ or $Z$, respectively, the unconditioned and every homodyne-conditioned adversarial state are normalized, their quantum entropies are finite, and
--
--   $$H(D)=g((1-t)\mu),\qquad H(D\mid W)=g(n_t),\qquad \chi(W;D)=g((1-t)\mu)-g(n_t).$$
--
--   Here $g(x)=(x+1)\log_2(x+1)-x\log_2x$, with the vacuum convention $g(0)=0$. Classical mutual informations in the two reconciliation orderings follow from the displayed differential entropies. The density and entropy integrals are integrable; the conditional density can depend on the outcome even though its entropy does not.
--
--   These formulas evaluate the information terms of the protocol; they do not assert operational achievability or identify its rates with capacity.
--
--   **Formalization Note** The state is constructed from full Fock amplitudes and the normalized Hermite homodyne kernel. The p.8 misprints in the second variance label, the $AC$ correlation, and the dimension and prefactor of Eq.(32) are corrected as recorded in the source-correction ledger; the consistent scalar entropy formulas are preserved.
-- source:
--   Unconstrained Capacities of Quantum Key Distribution and Entanglement Distillation for Pure-Loss Bosonic Broadcast Channels, arXiv:1706.06746v1, PDF p. 9, Supplement 3, Eqs.(33)–(46)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P19

open MeasureTheory

open scoped BigOperators ENNReal NNReal

open QAlgorithms.Papers.Independent.Dependency50.P30
  (PureLossBroadcastParameters thermalEntropyBits)

open QAlgorithms.Papers.Independent.Support50.P48
  (tmsvWeight vacuumAmplitude subsystem)

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Gap48.P13 (hermiteValue)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Supplement 3, PDF pp.8–9, (33)–(38),(40),(46): all classical and
quantum information terms required by (28),(29), evaluated on the actual
finite-energy TMSV/vacuum broadcast measurement experiment.

Source corrections (trap 30), verified visually on PDF p.8: the second b
following (30) means c, and f uses eta_C rather than eta_B. In (32), the
homodyne limit uses the measured 3x3 q block Q and density
exp(-x^T Q^{-1}x)/(pi^(3/2) sqrt(det Q)); the displayed 6x6 inverse and
prefactor are incompatible with a three-coordinate density. Consequently
(33) uses det Q. The six consistent entropy formulas (33)–(38) are retained.
The source's outcome-independent conditional covariance in (44) is used
only for the entropy, never to assert equal conditional density operators.
These corrections require independent moderation. -/
theorem gaussian_rate_evaluation (p : PureLossBroadcastParameters 2) (mu : ℝ≥0) :
    let v : ℝ := 2 * (mu : ℝ) + 1
    let b : ℝ := p.transmissivity 0
    let c : ℝ := p.transmissivity 1
    let h : Finset (Fin 3) → ℝ := measuredEntropyBits p mu
    IsDensity (detectedResource p mu) ∧
    (∀ S ∈ measuredSets, RegularMeasuredMarginal p mu S) ∧
    h Finset.univ = (1 / 2 : ℝ) * Real.logb 2
      ((Real.pi * Real.exp 1) ^ 3 * ((1 - (b + c) / 2) * (v - 1) + 1)) ∧
    h {0} = (1 / 2 : ℝ) * Real.logb 2 (Real.pi * Real.exp 1 * v) ∧
    h {1} = (1 / 2 : ℝ) * Real.logb 2
      (Real.pi * Real.exp 1 * (b / 2 * (v - 1) + 1)) ∧
    h {2} = (1 / 2 : ℝ) * Real.logb 2
      (Real.pi * Real.exp 1 * (c / 2 * (v - 1) + 1)) ∧
    h {0, 1} = (1 / 2 : ℝ) * Real.logb 2
      ((Real.pi * Real.exp 1) ^ 2 * ((1 - b / 2) * (v - 1) + 1)) ∧
    h {0, 2} = (1 / 2 : ℝ) * Real.logb 2
      ((Real.pi * Real.exp 1) ^ 2 * ((1 - c / 2) * (v - 1) + 1)) ∧
    (∀ i : Fin 2,
      let t := p.transmissivity i
      IsDensity (groupedJoint t mu) ∧
      IsDensity (groupedMarginal t mu) ∧
      oscillatorEntropyBits (groupedMarginal t mu) ≠ ⊤ ∧
      (oscillatorEntropyBits (groupedMarginal t mu)).toReal =
        thermalEntropyBits ((1 - (t : ℝ)) * (mu : ℝ)) ∧
      (∀ y : ℝ, 0 < receiverDensity t mu y ∧
        IsDensity (conditionalAdversary t mu y) ∧
        oscillatorEntropyBits (conditionalAdversary t mu y) ≠ ⊤ ∧
        (oscillatorEntropyBits (conditionalAdversary t mu y)).toReal =
          thermalEntropyBits (conditionalOccupation t mu)) ∧
      Integrable (receiverDensity t mu) ∧
      (∫ y : ℝ, receiverDensity t mu y) = 1 ∧
      Integrable (fun y : ℝ => receiverDensity t mu y *
        (oscillatorEntropyBits (conditionalAdversary t mu y)).toReal) ∧
      (∫ y : ℝ, receiverDensity t mu y *
        (oscillatorEntropyBits (conditionalAdversary t mu y)).toReal) =
          thermalEntropyBits (conditionalOccupation t mu) ∧
      adversaryHolevoBits t mu =
        thermalEntropyBits ((1 - (t : ℝ)) * (mu : ℝ)) -
          thermalEntropyBits (conditionalOccupation t mu)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P19

end
