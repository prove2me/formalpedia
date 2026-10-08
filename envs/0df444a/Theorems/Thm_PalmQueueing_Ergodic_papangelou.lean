-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_papangelou
-- name    : PalmQueueing.Ergodic.papangelou
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:22:56.37939+00:00
-- url     : https://prove2.me/theorems/1b334e21-98ac-47cc-a523-03f278a5c66d
-- title:
--   Theorem 1.9.2 — Papangelou's theorem
-- statement:
--   **Theorem 1.9.2 (Papangelou's theorem).** Let $N$ be a point process and
--   $\{\mathcal{F}_t\}$ be a history of $N$, both compatible with the flow $\{\theta_t\}$. Suppose
--   that the intensity $\lambda$ of $N$ is finite and non-null, and let $P^0_N$ be the Palm
--   probability associated with $(N,P)$. Suppose moreover that the $\mathcal{F}_t$-predictable
--   structure is adapted to $\{\theta_t\}$. Then $N$ admits a $(P,\mathcal{F}_t)$-intensity
--   $\{\lambda(t)\}$ **if and only if**
--   $$ P^0_N \ll P \quad \text{on} \quad \mathcal{F}_{0-} , \tag{1.9.2} $$
--   and in that case $\{\lambda(t)\}$ can be chosen of the form
--   $$ \lambda(t) = (\mu\circ\theta_t)\lambda , \tag{1.9.3} $$
--   where $\mu$ is the Radon-Nikodým derivative on $\mathcal{F}_{0-}$ of $P^0_N$ with respect to $P$:
--   $$ \mu = \frac{dP^0_N}{dP}\Big|_{\mathcal{F}_{0-}} . \tag{1.9.4} $$
--
--   The existence of a stochastic intensity is **exactly** the absolute continuity of the Palm
--   probability with respect to the stationary one on the strict past — a dynamic property and a
--   static one turn out to be the same thing. And when it holds the intensity is not merely some
--   process: it is the Radon-Nikodým derivative carried along the flow, scaled by $\lambda$.
--
--   The equivalence and the closed form are both stated; stating only the forward implication, or only
--   the existence of an intensity, would drop what the theorem is used for. Remark 1.9.4 gives the
--   compact expression that mission IV's Lemma 3.5.1 uses,
--   $$ E[f(Z(0))\lambda(0)] = \lambda E^0_N[f(Z(0))] , \tag{1.9.5} $$
--   for $\{Z(t)\}$ compatible with the flow with $Z(0)$ being $\mathcal{F}_{0-}$-measurable — hence
--   $\mathcal{F}_t$-predictable, in view of the predictable structure — and $f$ non-negative
--   measurable.
--
--   The hypothesis that the $\mathcal{F}_t$-predictable structure is adapted to $\{\theta_t\}$ is what
--   Theorem 1.8.1 supplies for an internal history, and it is what lets the proof write a predictable
--   $\{X(t)\}$ as $X(t,\omega) = v(t,\theta_t\omega)$ with $v(t,\cdot)$
--   $\mathcal{F}_{0-}$-measurable.
--
--   **Formalization Note.** "Compatible with the flow" for a history is the book's $\theta_t\mathcal{F}_s = \mathcal{F}_{s-t}$ (p.57), written `MeasurableSpace.comap (θ t) (H.F s) = H.F (s + t)`, i.e. $\mathbf{1}_A\circ\theta_t$ is $\mathcal{F}_{s+t}$-measurable for $A \in \mathcal{F}_s$, as the proof of Theorem 1.9.1 uses it. The joint measurability of $(t,\omega)\mapsto\theta_t\omega$ is a field of `Flow`. An $\mathcal{F}_t$-intensity is, by the definition of p.58, a non-negative *measurable* process, adapted, *locally integrable*, with $E[N(a,b]\mathbf{1}_A] = E[\int_a^b\lambda(t)dt\,\mathbf{1}_A]$ for $A\in\mathcal{F}_a$; joint measurability and ($P$-a.s.) local integrability are stated explicitly, the rest is `HasIntensity`. The predictable structure is the equality $\mathcal{P}(\mathcal{F}_t) = \tau(\mathcal{F}_t)$ of Theorem 1.8.1; the proof on p.67 uses both inclusions.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 66, Theorem 1.9.2

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Palm_StochasticIntensity

/-!
# Theorem 1.9.2: Papangelou's theorem (§1.9.2, p.66)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.9.2 (Papangelou's theorem)** (p.66). Let `N` be a point process and `{F_t}` be a
history of `N`, both `N` and `{F_t}` being compatible with the flow `{θ_t}`. Suppose that the
intensity `λ` of `N` is finite and non-null, and let `P⁰_N` be the Palm probability associated
with `(N, P)`. Suppose moreover that the `F_t`-predictable structure is adapted to `{θ_t}`. Then
`N` admits a `(P, F_t)`-intensity `{λ(t)}` **if and only if**

`(1.9.2)  P⁰_N ≪ P  on  F_{0−}`,

and in that case `{λ(t)}` can be chosen of the form

`(1.9.3)  λ(t) = (μ ∘ θ_t) λ`,

where `μ` is the Radon-Nikodým derivative on `F_{0−}` of `P⁰_N` with respect to `P`:

`(1.9.4)  μ = dP⁰_N/dP |_{F_{0−}}`.

The existence of a stochastic intensity is **exactly** the absolute continuity of the Palm
probability with respect to the stationary one on the strict past — a dynamic property and a
static one turn out to be the same. And when it holds, the intensity is not merely some process:
it is the Radon-Nikodým derivative carried along the flow, scaled by the intensity `λ`.

The equivalence is stated as an equivalence and the closed form (1.9.3)-(1.9.4) alongside it;
stating only the forward implication, or only the existence of an intensity, would drop what the
theorem is used for. Remark 1.9.4 gives the compact expression that mission `03` uses in Lemma
3.5.1:

`(1.9.5)  E[f(Z(0))λ(0)] = λ E⁰_N[f(Z(0))]`,

for `{Z(t)}` compatible with the flow with `Z(0)` `F_{0−}`-measurable — hence
`F_t`-predictable, in view of the predictable structure — and `f` non-negative measurable.

The hypothesis that the `F_t`-predictable structure is adapted to `{θ_t}` is what Theorem 1.8.1
supplies for an internal history, and it is what lets the proof write a predictable `{X(t)}` as
`X(t,ω) = v(t, θ_tω)` with `v(t, ·)` `F_{0−}`-measurable.

`hHcompat` is "both `N` and `{F_t}` being
compatible with the flow": `θ_t F_s = F_{s−t}` (p.57), written `comap θ_t F_s = F_{s+t}`. An
`F_t`-intensity is, by the definition of p.58, a non-negative measurable locally integrable process,
which is what the existential carries. -/
theorem papangelou (S : PalmSetting Ω) (H : History Ω)
    (hhist : H.IsHistoryOf S.N)
    (hHcompat : ∀ s t : ℝ, MeasurableSpace.comap (S.θ t) (H.F s) = H.F (s + t))
    (hstructure : H.predictableSigma = H.shiftSigma S.θ) :
    ((∃ lamProc : ℝ → Ω → ℝ, (Measurable fun p : ℝ × Ω => lamProc p.1 p.2) ∧
        (∀ᵐ ω ∂S.P, ∀ a b : ℝ, IntegrableOn (fun t => lamProc t ω) (Set.Ioc a b) volume) ∧
        HasIntensity H S.N S.P lamProc)
      ↔ ∀ A : Set Ω, MeasurableSet[H.zeroMinus] A → S.P A = 0 → S.P0 A = 0) ∧
    ((∀ A : Set Ω, MeasurableSet[H.zeroMinus] A → S.P A = 0 → S.P0 A = 0) →
      ∃ mu : Ω → ℝ,
        Measurable[H.zeroMinus] mu ∧
        (∀ (ω : Ω), 0 ≤ mu ω) ∧
        (∀ A : Set Ω, MeasurableSet[H.zeroMinus] A →
          S.P0 A = ∫⁻ ω in A, ENNReal.ofReal (mu ω) ∂S.P) ∧
        HasIntensity H S.N S.P (fun t ω => mu (S.θ t ω) * S.lam)) := by sorry

end PalmQueueing.Ergodic
