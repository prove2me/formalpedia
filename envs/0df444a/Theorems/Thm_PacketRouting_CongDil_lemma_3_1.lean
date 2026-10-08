-- Prove2me | Theorems.Thm_PacketRouting_CongDil_lemma_3_1
-- name    : PacketRouting.CongDil.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:03:00.148984+00:00
-- url     : https://prove2.me/theorems/9131ebcf-5fd3-4150-9e8e-b632c8519371
-- title:
--   Lemma 3.1, p. 8 — Lovász Local Lemma: probability ≤ p, dependence ≤ b, 4pb < 1 ⇒ no bad event with positive probability
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space and let $A_1,\dots,A_m\in\mathcal F$ be "bad" events. Suppose that
--
--   1. each bad event has probability at most $p$: $\mu(A_i)\le p$ for every $i$;
--   2. the family has dependence at most $b$, with $b\ge 1$: every $A_i$ is mutually independent of some set of at least $m-b-1$ other bad events.
--
--   **Lemma 3.1 (Lovász).** If $4pb<1$, then with probability greater than zero no bad event occurs:
--   $$
--   \mu\Bigl(\,\bigcap_{i=1}^m \overline{A_i}\Bigr)>0 .
--   $$
--
--   This is the probabilistic engine of the whole paper: every refinement step chooses random delays and uses the lemma to show that some choice of delays avoids every "too much congestion in a frame" event at once.
--
--   **Formalization Note** The page says "each occurring with probability $p$"; the statement assumes $\mu(A_i)\le p$, which is how the lemma is applied (p. 9: "$p\le\dots$"). The hypothesis $b\ge1$ is not on the page but is needed: with $b=0$ a single event of probability $1$ satisfies $4pb=0<1$ and the conclusion fails. Every application in the paper has $b\ge1$.
-- source:
--   Leighton, Maggs & Rao, Packet routing and job-shop scheduling in O(congestion + dilation) steps, authors' manuscript (preprint of Combinatorica 14 (1994), DOI 10.1007/BF01215349), p. 8, Lemma 3.1

import Mathlib
import Definitions.Def_PacketRouting_CongDil_Dependence

namespace PacketRouting.CongDil

open MeasureTheory

/-- Lemma 3.1 (Lovász Local Lemma, Leighton–Maggs–Rao, p. 8): let `A₁, …, A_m` be measurable
"bad" events in a probability space, each of probability at most `p`, with dependence at most
`b ≥ 1`. If `4 p b < 1`, then with probability greater than zero no bad event occurs. -/
theorem lemma_3_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (A : Fin m → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    (p : ℝ) (b : ℕ) (hp : ∀ i, μ.real (A i) ≤ p) (hdep : HasDependenceAtMost μ A b)
    (hb : 1 ≤ b) (h4 : 4 * p * b < 1) :
    0 < μ (⋂ i, (A i)ᶜ) := by sorry

end PacketRouting.CongDil
