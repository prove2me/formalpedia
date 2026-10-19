-- Prove2me | Theorems.Thm_QAlgorithms_Papers_RoadmapX05_probabilisticCancellation_estimator
-- name    : QAlgorithms.Papers.RoadmapX05.probabilisticCancellation_estimator
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T18:47:15.503964+00:00
-- url     : https://prove2.me/theorems/068084e3-2ef1-45d0-98ac-b6de4b5b49f2
-- title:
--   Probabilistic error cancellation: unbiasedness, variance, precision and run overhead
-- statement:
--   Let $\Omega=\{\mathcal O_1,\ldots,\mathcal O_m\}$ be a finite family of known implementable completely positive trace-preserving maps on an $n$-qubit device. Maps may include noisy initialization and need not be unitary or unital. Let $\beta$ be a length-$L$ word in a fixed finite unitary gate family, with composite unitary $U_\beta$. Assume a supplied exact quasi-probability representation, fixed before all experimental outcomes:
--
--   $$
--   U_\beta XU_\beta^\dagger=\gamma_\beta\sum_{\alpha\in\Omega_L}P_\beta(\alpha)\sigma_\beta(\alpha)\mathcal O_\alpha(X)\quad\text{for every operator }X,
--   $$
--
--   where $\gamma_\beta\ge1$, $P_\beta$ is a probability distribution on length-$L$ noisy words, $\sigma_\beta(\alpha)\in\{-1,1\}$, and $\mathcal O_\alpha=\mathcal O_{\alpha_L}\circ\cdots\circ\mathcal O_{\alpha_1}$. Each experiment starts from a fresh $\rho_0=|0\rangle\langle0|^{\otimes n}$ and ends with ideal computational-basis measurement of every qubit. Let $A=\operatorname{diag}(a_x)$ with $a_x\in[-1,1]$. Set $E(\alpha)=\operatorname{Tr}(A\mathcal O_\alpha(\rho_0))$ and $E^*=\operatorname{Tr}(AU_\beta\rho_0U_\beta^\dagger)$.
--
--   Conditioned on any noisy word, the readout $a_x$ has mean $E(\alpha)$ and variance at most $1$. Moreover,
--
--   $$
--   E^*=\gamma_\beta\sum_\alpha P_\beta(\alpha)\sigma_\beta(\alpha)E(\alpha).
--   $$
--
--   For a full trial, first draw $\alpha\sim P_\beta$, then draw its fresh conditional readout $x$ and report $Y=\gamma_\beta\sigma_\beta(\alpha)a_x$. This gives $|Y|\le\gamma_\beta$, $\mathbb EY=E^*$ and $\operatorname{Var}(Y)\le\gamma_\beta^2$. For every positive integer $M$, perform $M$ independent full trials and compute the paper's estimator
--
--   $$
--   \widehat E=\frac{\gamma_\beta}{M}\sum_{i=1}^M\sigma_\beta(\alpha^i)a_{x^i}.
--   $$
--
--   The product trial law has total mass one, and
--
--   $$
--   \mathbb E\widehat E=E^*,\qquad \operatorname{Var}(\widehat E)\le\frac{\gamma_\beta^2}{M},\qquad
--   \Pr\{|\widehat E-E^*|\ge t\}\le2\exp\!\left(-\frac{Mt^2}{2\gamma_\beta^2}\right)\quad(t>0).
--   $$
--
--   The computed experiment uses exactly $M$ noisy-circuit runs and $ML$ channel applications, all on the same $n$-qubit register. For every $\delta>0$, the rounded Eq. (9) budget $M=\lceil(\gamma_\beta/\delta)^2\rceil$ is positive and satisfies
--
--   $$
--   \gamma_\beta^2\le M\delta^2<\gamma_\beta^2+\delta^2,\qquad
--   \Pr\{|\widehat E-E^*|\ge c\delta\}\le2e^{-c^2/2}\quad(c>0).
--   $$
--
--   These universal numerical bounds witness the paper's bounded-variance, Monte Carlo precision and $\gamma_\beta^2$ run-overhead claims. The overhead describes a sufficient sampling budget relative to the noiseless $\delta^{-2}$ scale, without claiming optimality for every observable.
--
--   **Formalization Note** The theorem uses the supplied QPR distribution directly and makes no classical runtime claim; the paper's efficient sampling and computable-sign premises concern its implementation. Locality and depth preservation require the chosen QPR construction and are not inferred from the decomposition alone. The displayed tail bound spells out “$O(\delta)$ w.h.p.”: choosing a sufficiently large fixed $c$ makes the failure small, but fixed $c$ does not imply a failure probability vanishing with $\delta$.
-- source:
--   Error mitigation for short-depth quantum circuits, arXiv:1612.02058v3, Probabilistic error cancellation, Eqs. (7)–(10); continuation p.4; duplicate Eqs. (41)–(42), p.10, PDF p. 3. https://arxiv.org/abs/1612.02058v3 . PDF SHA-256: 1bb069492859f97df6674a403f0f1bbc0b7d979ad5cbb3483ac2eded787886e2.

import Definitions.Def_QAlgorithms_Defs_CancellationResources
set_option autoImplicit false

noncomputable section

open scoped Matrix

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.RoadmapX05

open QAlgorithms.ProbabilisticCancellation

/-- Temme, Bravyi and Gambetta, arXiv:1612.02058v3, PDF pp.3--4,
Eqs.(7)--(10), with the duplicate QPR identities (41)--(42) on p.10.
For a supplied exact signed decomposition, the computed fresh-trial estimator
has the ideal expectation and bounded variance. Independent repetitions give
the displayed Hoeffding bound and the rounded Eq.(9) run budget. The numerical
constants are universal witnesses to the printed O claims. At that budget,
error c * delta has failure at most 2 * exp(-c^2/2); no vanishing-failure
claim at fixed c is intended. Only circuit runs and channel applications are
counted; efficient sampling and sign evaluation are implementation provenance.
Local supports and depth preservation concern the source's QPR constructions,
not this conditional statistical result. -/
theorem probabilisticCancellation_estimator
    {n m k L : ℕ} (B : NoisyCircuits.ChannelBasis n m)
    (idealBasis : Fin k → Matrix.unitaryGroup (Qubits n) ℂ)
    (beta : Fin L → Fin k)
    (Q : QPR B L ((List.ofFn fun j => idealBasis (beta j)).reverse.prod))
    (A : DiagonalReadout n) :
    let ideal := ((List.ofFn fun j => idealBasis (beta j)).reverse.prod :
      Matrix.unitaryGroup (Qubits n) ℂ)
    let target := effectProb (Matrix.diagonal fun z => (A.value z : ℂ))
      (conjSuperop (ideal : Matrix _ _ ℂ) (pureDensity (zeroKet n)))
    let noisy := fun alpha : Fin L → Fin m => circuitExpectation B (List.ofFn alpha) A
    let shot := fun trial : (Fin L → Fin m) × Qubits n => shotEstimator Q A trial
    (∀ alpha : Fin L → Fin m,
      (∑ z, (NoisyCircuits.computationalReadoutLaw B (List.ofFn alpha) z).toReal *
        A.value z) = noisy alpha ∧
      (∑ z, (NoisyCircuits.computationalReadoutLaw B (List.ofFn alpha) z).toReal *
        (A.value z - noisy alpha) ^ 2) ≤ 1) ∧
    target = Q.gamma * ∑ alpha, (Q.words alpha).toReal *
      (if Q.sign alpha then (1 : ℝ) else -1) * noisy alpha ∧
    (∀ trial, |shot trial| ≤ Q.gamma) ∧
    (∑ trial, (trialLaw Q trial).toReal * shot trial) = target ∧
    (∑ trial, (trialLaw Q trial).toReal * (shot trial - target) ^ 2) ≤ Q.gamma ^ 2 ∧
    (∀ (M : ℕ) (hM : 0 < M),
      let weight := repeatedLaw Q M hM
      let estimate := sampleMean Q A M hM
      (∑ trials, weight trials) = 1 ∧
      (∀ trials, estimate trials = Q.gamma / (M : ℝ) *
        ∑ i, (if Q.sign (trials i).1 then (1 : ℝ) else -1) * A.value (trials i).2) ∧
      (∑ trials, weight trials * estimate trials) = target ∧
      (∑ trials, weight trials * (estimate trials - target) ^ 2) ≤ Q.gamma ^ 2 / M ∧
      (∀ t : ℝ, 0 < t →
        (∑ trials ∈ Finset.univ.filter (fun trials => t ≤ |estimate trials - target|),
          weight trials) ≤ 2 * Real.exp (-((M : ℝ) * t ^ 2) / (2 * Q.gamma ^ 2))) ∧
      experimentRunCount Q M hM = M ∧ experimentOperationCount Q M hM = M * L) ∧
    (∀ (delta : ℝ) (hdelta : 0 < delta),
      let M := precisionBudget Q.gamma delta Q.gamma_ge hdelta
      ∃ hM : 0 < M,
        experimentRunCount Q M hM = M ∧
        Q.gamma ^ 2 ≤ (M : ℝ) * delta ^ 2 ∧
        (M : ℝ) * delta ^ 2 < Q.gamma ^ 2 + delta ^ 2 ∧
        (∀ c : ℝ, 0 < c →
          (∑ trials ∈ Finset.univ.filter (fun trials =>
              c * delta ≤ |sampleMean Q A M hM trials - target|),
            repeatedLaw Q M hM trials) ≤ 2 * Real.exp (-(c ^ 2) / 2))) := by sorry

end QAlgorithms.Papers.RoadmapX05
