-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_conditional_poisson
-- name    : PalmQueueing.Ergodic.conditional_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:33:06.088973+00:00
-- url     : https://prove2.me/theorems/2685098f-ccdc-44ba-b7d8-827c23ff6c41
-- title:
--   Theorem 1.8.2 — Watanabe's characterization of Poisson processes
-- statement:
--   **Theorem 1.8.2.** Let $N$ be a simple point process, and let $\{\mathcal{F}_t\}$ be a
--   history of the form
--   $$ \mathcal{F}_t = \mathcal{F}^N_t \vee \mathcal{G} \tag{1.8.11} $$
--   for some arbitrary $\sigma$-field $\mathcal{G}$. Let $\{\lambda(t)\}$ be a measurable stochastic
--   process, locally integrable, such that for all $t$, the random variable $\lambda(t)$ is
--   $\mathcal{G}$-measurable. If $N$ admits the $\mathcal{F}_t$-intensity $\{\lambda(t)\}$, then $N$
--   is a **$\mathcal{G}$-conditional Poisson process** with $\mathcal{G}$-conditional associated
--   intensity measure $E[N(C)\mid\mathcal{G}] = \int_C \lambda(t)dt$, that is, by definition: for all
--   $u \in \mathbb{R}$, all $(a,b] \subset \mathbb{R}$,
--   $$ E\big[e^{iuN(a,b]} \,\big|\, \mathcal{G} \vee \mathcal{F}^N_a\big]
--   = \exp\Big\{(e^{iu}-1)\int_a^b \lambda(t)dt\Big\} . \tag{1.8.12} $$
--
--   A stochastic intensity that carries no information beyond $\mathcal{G}$ forces the process to be
--   Poisson conditionally on $\mathcal{G}$ — and the conditional characteristic function is the
--   *exact* Poisson one, with the compensator as its parameter. Taking $\mathcal{G}$ trivial and
--   $\lambda$ constant recovers the ordinary Poisson process, which is the equivalence Remark 3.3.1 of
--   Chapter 3 invokes to explain the name PASTA.
--
--   "This result plays a role in queueing theory, especially for proving that some streams in a
--   queueing network are or are not Poissonian."
--
--   Two details of the conditioning are load-bearing. The conditioning $\sigma$-field is
--   $\mathcal{G}\vee\mathcal{F}^N_a$ — the external information **and** the process' own past up to
--   $a$ — not $\mathcal{G}$ alone; the conclusion is that the increment beyond $a$ is conditionally
--   Poisson given everything known at $a$. And the history is required to be of the form (1.8.11),
--   which is what makes "$\lambda(t)$ is $\mathcal{G}$-measurable" a restriction rather than a
--   tautology.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 61, Theorem 1.8.2

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Palm_StochasticIntensity

/-!
# Theorem 1.8.2: Watanabe's characterization of Poisson processes (§1.8.4, p.61)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.8.2** (§1.8.4 "Watanabe's Characterization of Poisson Processes", p.61). Let `N`
be a simple point process, and let `{F_t}` be a history of the form

`(1.8.11)  F_t = F_t^N ∨ G`

for some arbitrary σ-field `G`, carried below as a history constant in `t` so that it is a
sub-σ-field without being an ambient instance. Let `{λ(t)}` be a measurable stochastic process, locally
integrable, such that for all `t`, the random variable `λ(t)` is `G`-measurable. If `N` admits the
`F_t`-intensity `{λ(t)}`, then `N` is a **`G`-conditional Poisson process** with `G`-conditional
associated intensity measure `E[N(C) | G] = ∫_C λ(t)dt`, that is, by definition: for all `u ∈ ℝ`,
all `(a,b] ⊂ ℝ`,

`(1.8.12)  E[e^{iuN(a,b]} | G ∨ F^N_a] = exp{(e^{iu} − 1) ∫_a^b λ(t)dt}`.

A stochastic intensity that carries no information beyond `G` forces the process to be Poisson
conditionally on `G` — and the conditional characteristic function is the *exact* Poisson one,
with the compensator as its parameter. Taking `G` trivial and `λ` constant recovers the ordinary
Poisson process, which is the equivalence Remark 3.3.1 of Chapter 3 invokes to explain the name
PASTA.

"This result plays a role in queueing theory, especially for proving that some streams in a
queueing network are or are not Poissonian."

Two details of the conditioning are load-bearing. The conditioning σ-field is `G ∨ F^N_a` — the
external information **and** the process' own past up to `a` — not `G` alone; the conclusion is
that the increment beyond `a` is conditionally Poisson given everything known at `a`. And the
history is required to be of the form (1.8.11), which is what makes `λ(t)` `G`-measurable a
restriction rather than a tautology. -/
theorem conditional_poisson (P : Measure Ω) [IsProbabilityMeasure P]
    (N : PointProcess Ω) (Gh : History Ω) (hGconst : ∀ s t : ℝ, Gh.F s = Gh.F t)
    (HN H : History Ω)
    (hHN : ∀ (t : ℝ) (C : Set ℝ), MeasurableSet C → C ⊆ Set.Iic t →
      Measurable[HN.F t] fun ω => N.count ω C)
    (hform : ∀ t : ℝ, H.F t = HN.F t ⊔ Gh.F t)
    (lamProc : ℝ → Ω → ℝ)
    (hjoint : Measurable fun p : ℝ × Ω => lamProc p.1 p.2)
    (hGmeas : ∀ t : ℝ, Measurable[Gh.F 0] (lamProc t))
    (hloc : ∀ (a b : ℝ) (ω : Ω), IntegrableOn (fun t => lamProc t ω) (Set.Ioc a b) volume)
    (hintensity : HasIntensity H N P lamProc)
    (u : ℝ) (a b : ℝ) (hab : a ≤ b) :
    condExp (Gh.F 0 ⊔ HN.F a) P
        (fun ω => Complex.exp (Complex.I * u * ((N.count ω (Set.Ioc a b)).toReal)))
      =ᵐ[P] fun ω => Complex.exp ((Complex.exp (Complex.I * u) - 1) *
        ((∫ t in Set.Ioc a b, lamProc t ω ∂(volume : Measure ℝ) : ℝ) : ℂ)) := by sorry

end PalmQueueing.Ergodic
