-- Prove2me | Theorems.Thm_SingularQDS_DomainAlg_eq_12_duhamel
-- name    : SingularQDS.DomainAlg.eq_12_duhamel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:44:42.707328+00:00
-- url     : https://prove2.me/theorems/f63e6393-6f4b-46c1-a53d-5fb0eb9d9cd6
-- title:
--   (12), p. 5 — ⟨ϕ|T_t[X]|ψ⟩ = ⟨ϕ|T⁰_t[X]|ψ⟩ + ∫₀ᵗ ψ(s)ϕ̄(s) Tr ΩT_{t−s}[X] ds for ϕ, ψ ∈ AC¹(ℝ₊)
-- statement:
--   In the setting of the rank-one reset of the left shift on $\mathcal H = L^2(\mathbb R_+)$ (an arbitrary density operator $\Omega$, the shift semigroup $T^0_t[X] = W_t^* X W_t$, and the minimal perturbed semigroup $T_t = (S_t)^*$), let $\mathcal D = AC^1(\mathbb R_+)$ be the space of absolutely continuous functions $\varphi$ on $\mathbb R_+$ with $\varphi' \in L^2(\mathbb R_+)$. The perturbed backward master equation is equivalent to the integral equation
--
--   $$\langle\varphi|T_t[X]|\psi\rangle = \langle\varphi|T^0_t[X]|\psi\rangle + \int_0^t \operatorname{Tr}\Lambda\bigl[S^0_s[|\psi\rangle\langle\varphi|]\bigr]\,T_{t-s}[X]\,ds, \qquad \varphi,\psi \in \mathcal D .$$
--
--   Since $\Lambda[S^0_s[|\psi\rangle\langle\varphi|]] = \Omega\,\psi(s)\,\overline{\varphi(s)}$, this reads: for every bounded operator $X$, every $t \ge 0$ and all $\varphi, \psi \in \mathcal D$,
--
--   $$\langle\varphi|T_t[X]|\psi\rangle = \langle\varphi|T^0_t[X]|\psi\rangle + \int_0^t \psi(s)\,\overline{\varphi(s)}\,\operatorname{Tr}\Omega\, T_{t-s}[X]\,ds .$$
--
--   Rearranged and divided by $t$, this is the identity (13) on which the proof of Lemma 4 rests.
--
--   **Formalization Note** The statement is the specialized form (after (6), (9)). Membership $\varphi \in AC^1(\mathbb R_+)$ is encoded as in the published `H1Trace`: an $L^2$ class `phi`, a locally absolutely continuous representative `Phi` equal to it almost everywhere, and an $L^2$ class `dphi` that is the derivative of `Phi` almost everywhere; likewise for $\psi$. Only the continuous representatives are evaluated at $s$. $\langle\varphi|A|\psi\rangle$ is Mathlib's inner product, conjugate-linear in its first argument. The integral is the interval integral over $[0,t]$ with $t \ge 0$, so $t - s \ge 0$ and no time is clamped; the integrand is continuous on $[0,t]$. $\operatorname{Tr}\Omega Y$ is the published basis trace of $\Omega Y$.
-- source:
--   Holevo, On singular perturbations of quantum dynamical semigroups, arXiv:1706.04866v5, p. 5, (12) together with the following sentence (via (6), (9))

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P06
open QAlgorithms.Papers.Independent.Renew46.P06
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass State NuclearRepresentation traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup DynamicalSemigroup IsCPOnBoundedOperators IsUnitalQDS IsRelaxingEvolution)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain DomainPerturbation IsMinimalPerturbation)

namespace SingularQDS.DomainAlg

/-- arXiv:1706.04866v5, p. 5, (12) with (6), (9): for ϕ, ψ ∈ AC¹(ℝ₊) (continuous
representatives Phi, Psi, a.e. derivatives dphi, dpsi ∈ L²), every bounded X and t ≥ 0,
⟨ϕ|T_t[X]|ψ⟩ = ⟨ϕ|T⁰_t[X]|ψ⟩ + ∫₀ᵗ ψ(s) conj(ϕ(s)) Tr Ω T_{t−s}[X] ds. -/
theorem eq_12_duhamel (b : HilbertBasis ℕ ℂ HalfLine) (Omega : State b)
    (W : ContractionSemigroup HalfLine) (hShift : IsLeftShift W)
    (Szero : TraceEvolution b) (Tzero : Evolution) (hPair : IsShiftPair b W Szero Tzero)
    (P : DomainPerturbation Szero) (S : TraceEvolution b) (T : Evolution)
    (hReset : IsResetConstruction b Szero Omega P S T)
    (phi dphi psi dpsi : HalfLine) (Phi Psi : ℝ → ℂ)
    (hPhi : Phi =ᵐ[halfLineMeasure] phi ∧ LocallyAC Phi ∧
      ∀ᵐ x ∂halfLineMeasure, HasDerivAt Phi (dphi x) x)
    (hPsi : Psi =ᵐ[halfLineMeasure] psi ∧ LocallyAC Psi ∧
      ∀ᵐ x ∂halfLineMeasure, HasDerivAt Psi (dpsi x) x)
    (X : HalfLine →L[ℂ] HalfLine) (t : ℝ) (ht : 0 ≤ t) :
    inner ℂ phi (T.maps t.toNNReal X psi) =
      inner ℂ phi (Tzero.maps t.toNNReal X psi) +
        ∫ s in (0 : ℝ)..t, Psi s * star (Phi s) *
          operatorTrace b (Omega.val.val.comp (T.maps (t - s).toNNReal X)) := by sorry

end SingularQDS.DomainAlg
