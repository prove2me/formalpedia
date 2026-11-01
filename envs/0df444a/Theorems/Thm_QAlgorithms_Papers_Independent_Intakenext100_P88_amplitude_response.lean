-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P88_amplitude_response
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P88.amplitude_response
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:29:25.915427+00:00
-- url     : https://prove2.me/theorems/bbf2b75c-517b-4743-ba7f-6d1c663b7ff8
-- title:
--   Finite amplitude dQNTK response and bound
-- statement:
--   Use the same ordered unitary circuit and normalized feature states, but output all complex amplitudes $z_{x,i}=\langle i|U\phi(x)\rangle$, $i=1,\ldots,h$. Duplicate each output as $\mathcal z_{x,0,i}=z_{x,i}$ and $\mathcal z_{x,1,i}=\overline{z_{x,i}}$. The worldsheet index therefore records whether an amplitude is conjugated. For real parameters, write $\mathcal J_{\mu\ell}=\partial_{\theta_\ell}\mathcal z_\mu$.
--
--   Absorb the reference angles, rescale by $\delta>0$, and compute doubled jets $J_{\mu\ell}$ and $H_{\mu,k\ell}$ at zero directly from the actual circuit. For initial angles $v$, set $V_{\mu\ell}=\sum_k H_{\mu,k\ell}v_k$, $K=JJ^\dagger$, and $D=JV^\dagger+VJ^\dagger$, all restricted to doubled training indices. Let $e$ be the quadratic Taylor amplitude output minus the complex labels and their conjugates. With $q=\eta/2>0$ and $B=1-qK$, the retained coefficient recurrences $F_{t+1}=BF_t$ and $I_{t+1}=BI_t-qDF_t$, initialized by $(F_0,I_0)=(e,0)$, satisfy
--   $$
--   F_t=B^t e,\qquad I_0=0,\qquad I_{t+1}=-q\sum_{s=0}^{t}B^{t-s}DB^s e,\qquad
--   \|I_{t+1}\|_2\le q(t+1)\|B\|_2^t\|D\|_2\|e\|_2.
--   $$
--   The retained residual is $F_t+I_t$. This is a fixed-time coefficient response and requires no impossible full doubled inverse or nonlinear remainder estimate.
-- source:
--   Representation Learning via Quantum Neural Tangent Kernels, arXiv:2111.04225v3, PDF p. 33, SM Eqs.(170)-(173)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P88

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P88

open scoped BigOperators ComplexConjugate Topology NNReal ComplexOrder

open MeasureTheory ProbabilityTheory Filter

/-- PDF p.33 Eqs.(170)-(173): finite doubled-amplitude response and L2 norm bound.
All jets come from the original U; the response retains conjugation symmetry and eta/2.
The coefficient recurrence needs no inverse of the necessarily singular doubled kernel. -/
theorem amplitude_response {D T : Type*} [Fintype T] [DecidableEq T] {h L : ℕ}
    (M : AmplitudeModel D h L) (embed : T ↪ D)
    (delta eta : ℝ) (hdelta : 0 < delta) (heta : 0 < eta)
    (v : Fin L → ℝ) (y : T × Fin h → ℂ) :
    let incl := fun a : T × Bool × Fin h => (embed a.1, a.2.1, a.2.2)
    let K : Matrix (T × Bool × Fin h) (T × Bool × Fin h) ℂ := fun a b =>
      frozenAmplitudeKernel M delta (incl a) (incl b)
    let D : Matrix (T × Bool × Fin h) (T × Bool × Fin h) ℂ := fun a b =>
      deltaAmplitudeKernel M delta v (incl a) (incl b)
    let e : EuclideanSpace ℂ (T × Bool × Fin h) := WithLp.toLp 2 (fun a =>
      quadraticAmplitude M delta v (incl a) -
        (if a.2.1 then star (y (a.1, a.2.2)) else y (a.1, a.2.2)))
    let R := retainedResidual K D (eta / 2) e
    (∀ t, (R t).1 = l2Action ((1 - (eta / 2) • K) ^ t) e) ∧
    (R 0).2 = 0 ∧
    (∀ t : ℕ, (R (t + 1)).2 = -(eta / 2 : ℝ) •
      (∑ s ∈ Finset.range (t + 1),
        l2Action (((1 - (eta / 2) • K) ^ (t - s)) * D * ((1 - (eta / 2) • K) ^ s)) e)) ∧
    ∀ t : ℕ, ‖(R (t + 1)).2‖ ≤ (eta / 2) * ((t : ℝ) + 1) *
      QAlgorithms.specNorm (1 - (eta / 2) • K) ^ t * QAlgorithms.specNorm D * ‖e‖ := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P88

end
