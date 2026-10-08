-- Prove2me | Theorems.Thm_PalmQueueing_Ergodic_mecke_poisson
-- name    : PalmQueueing.Ergodic.mecke_poisson
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T22:26:51.746582+00:00
-- url     : https://prove2.me/theorems/71926643-4123-4158-a08e-41413555e667
-- title:
--   Theorem 1.9.3 — Mecke's characterization of Poisson processes
-- statement:
--   **Theorem 1.9.3 (Mecke's characterization of Poisson processes).** Let $N$ be a point
--   process and $\{\mathcal{F}_t\}$ be a history of $N$, both compatible with the flow
--   $\{\theta_t\}$. Suppose that $N$ has a finite intensity $\lambda$, and let $P^0_N$ be the Palm
--   probability associated with $(N,\theta_t)$. A necessary and sufficient condition for $N$ to be a
--   Poisson process — i.e. a process such that, for all $(a,b] \subset \mathbb{R}$, the random
--   variable $N(a,b]$ is $P$-independent of $\mathcal{F}_a$ — is
--   $$ P \equiv P^0_N \quad \text{on} \quad \mathcal{F}_{0-} . \tag{1.9.7} $$
--
--   The Palm probability is what the process looks like **from one of its own points**, and $P$ is
--   what it looks like from a deterministic instant. Mecke's theorem says the two views agree on the
--   strict past exactly when the process is Poisson — the deepest expression of the Poisson process'
--   lack of memory: seeing a point at the origin tells you nothing about what came before it.
--
--   It is proved in one line from the two theorems before it: "In view of Theorem 1.9.2, this follows
--   from Watanabe's theorem (Theorem 1.8.2)." By Papangelou, $P \equiv P^0_N$ on $\mathcal{F}_{0-}$
--   gives $\mu \equiv 1$ and hence the constant intensity $\lambda(t) \equiv \lambda$; Watanabe turns
--   a constant intensity into the Poisson property.
--
--   Stated as an equivalence. Both directions are used: one to recognise a Poisson process, the other
--   to compute with $P^0_N$ as if it were $P$.
--
--   **Formalization Note.** "Compatible with the flow" for a history is the book's $\theta_t\mathcal{F}_s = \mathcal{F}_{s-t}$ (p.57), written `MeasurableSpace.comap (θ t) (H.F s) = H.F (s + t)`, i.e. $\mathbf{1}_A\circ\theta_t$ is $\mathcal{F}_{s+t}$-measurable for $A \in \mathcal{F}_s$, as the proof of Theorem 1.9.1 uses it. The joint measurability of $(t,\omega)\mapsto\theta_t\omega$ is a field of `Flow`.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 68, Theorem 1.9.3

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Palm_StochasticIntensity

/-!
# Theorem 1.9.3: Mecke's characterization of Poisson processes (§1.9.2, p.68)
-/

namespace PalmQueueing.Ergodic

open MeasureTheory
open PalmQueueing.Palm

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Theorem 1.9.3 (Mecke's characterization of Poisson processes)** (p.68). Let `N` be a point
process and `{F_t}` a history of `N`, both compatible with the flow `{θ_t}`. Suppose that `N` has
a finite intensity `λ`, and let `P⁰_N` be the Palm probability associated with `(N, θ_t)`. A
necessary and sufficient condition for `N` to be a Poisson process — that is, a process such that
for all `(a,b] ⊂ ℝ`, the random variable `N(a,b]` is `P`-independent of `F_a` — is

`(1.9.7)  P ≡ P⁰_N  on  F_{0−}`.

The Palm probability is what the process looks like **from one of its own points**, and `P` is
what it looks like from a deterministic instant. Mecke's theorem says these two views agree on the
strict past exactly when the process is Poisson. That is the deepest expression of the "lack of
memory" of the Poisson process: seeing a point at the origin tells you nothing about what came
before it.

It sits directly beside Slivnyak's theorem, which is the same statement read on the whole σ-field
rather than on `F_{0−}`, and it is proved in one line from Papangelou's theorem (Theorem 1.9.2)
and Watanabe's (Theorem 1.8.2): by Theorem 1.9.2, `P ≡ P⁰_N` on `F_{0−}` gives `μ ≡ 1`, hence the
constant intensity `λ(t) ≡ λ`, and Watanabe turns a constant intensity into the Poisson property.

The equivalence is stated as an equivalence. Both directions are used: one to recognise a Poisson
process, the other to compute with `P⁰_N` as if it were `P`.

`hHcompat` is "both compatible with the flow":
`θ_t F_s = F_{s−t}` (p.57), written `comap θ_t F_s = F_{s+t}`. -/
theorem mecke_poisson (S : PalmSetting Ω) (H : History Ω)
    (hhist : H.IsHistoryOf S.N)
    (hHcompat : ∀ s t : ℝ, MeasurableSpace.comap (S.θ t) (H.F s) = H.F (s + t)) :
    (∀ a b : ℝ, a ≤ b → ∀ A : Set Ω, MeasurableSet[H.F a] A →
        ∀ B : Set ENNReal, MeasurableSet B →
        S.P ({ω | S.N.count ω (Set.Ioc a b) ∈ B} ∩ A)
          = S.P {ω | S.N.count ω (Set.Ioc a b) ∈ B} * S.P A) ↔
      ∀ A : Set Ω, MeasurableSet[H.zeroMinus] A → S.P A = S.P0 A := by sorry

end PalmQueueing.Ergodic
