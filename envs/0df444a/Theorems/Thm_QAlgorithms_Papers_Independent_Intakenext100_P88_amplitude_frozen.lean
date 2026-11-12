-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_amplitude_frozen
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.amplitude_frozen
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T08:28:55.779991+00:00
-- url     : https://prove2.me/theorems/df5bf783-d916-4ed7-b4cd-9339fc9db0b0
-- title:
--   Finite frozen doubled-amplitude training solution
-- statement:
--   Use the same ordered unitary circuit and normalized feature states, but output all complex amplitudes $z_{x,i}=\langle i|U\phi(x)\rangle$, $i=1,\ldots,h$. Duplicate each output as $\mathcal z_{x,0,i}=z_{x,i}$ and $\mathcal z_{x,1,i}=\overline{z_{x,i}}$. The worldsheet index therefore records whether an amplitude is conjugated. For real parameters, write $\mathcal J_{\mu\ell}=\partial_{\theta_\ell}\mathcal z_\mu$.
--
--   Absorb the reference angles and rescale by $\delta>0$. Let $J$ now be the doubled derivative with respect to $\varphi$ at zero, and restrict $K=JJ^\dagger$ to all doubled training coordinates $A\times\{0,1\}\times\{1,\ldots,h\}$. The initial residual $e$ is the first Taylor amplitude output at initial rescaled angles $v$ minus arbitrary complex training labels and their conjugates. For $\eta>0$, the frozen recurrence $\epsilon_{t+1}=\epsilon_t-(\eta/2)K\epsilon_t$ has the solution
--   $$
--   \epsilon_t=\bigl(1-(\eta/2)K\bigr)^t e,\qquad t\in\mathbb N.
--   $$
--   This finite solution preserves the real-loss normalization and requires no doubled-kernel inverse.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 30, SM Eqs.(152)-(154)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF pp.30-31 Eqs.(152)-(154): finite frozen amplitude solution on doubled training
indices. The real gradient of half the complex squared loss produces eta/2.
No inverse or asymptotic interpolation claim is included. -/
theorem amplitude_frozen {D T : Type*} [Fintype T] [DecidableEq T] {h L : ℕ}
    (M : AmplitudeModel D h L) (embed : T ↪ D)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (v : Fin L → ℝ) (y : T × Fin h → ℂ) (t : ℕ) :
    let incl := fun a : T × Bool × Fin h => (embed a.1, a.2.1, a.2.2)
    let K : Matrix (T × Bool × Fin h) (T × Bool × Fin h) ℂ := fun a b =>
      frozenAmplitudeKernel M delta (incl a) (incl b)
    let e : EuclideanSpace ℂ (T × Bool × Fin h) := WithLp.toLp 2 (fun a =>
      doubledAmplitude M 0 (incl a) + (∑ l, amplitudeJet M delta (incl a) l * (v l : ℂ)) -
        (if a.2.1 then star (y (a.1, a.2.2)) else y (a.1, a.2.2)))
    frozenResidual K (eta / 2) e t = l2Action ((1 - (eta / 2) • K) ^ t) e := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
