-- Prove2me | Theorems.Thm_RGGDetect_lemma_1
-- name    : RGGDetect.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:57.845204+00:00
-- url     : https://prove2.me/theorems/13058d59-dded-4315-8309-89647656ec4c
-- title:
--   Lemma 1 — KL divergence bounded by a truncated $\chi^2$ divergence
-- statement:
--   Let $P,Q$ be probability measures on a finite set $\Omega$ with $P\ll Q$, let $\Lambda=dP/dQ$, and let $q_*=\min_{\omega\in\Omega}Q(\omega)$. Then for every $T\subseteq\Omega$,
--
--   $$
--   \mathrm{KL}(P\|Q)\le\int_T(\Lambda-1)^2\,dQ+P(T^c)\log\frac1{q_*}+Q(T^c).
--   $$
--
--   This elementary inequality converts the KL divergence of the new row's conditional law into a truncated $\chi^2$-divergence plus tail terms, the first step of Theorem 2.
--
--   **Formalization Note** $\Lambda(\omega)=P\{\omega\}/Q\{\omega\}$. The bound is stated for every $q>0$ that is at most every positive atom of $Q$.
--
--   Differences from the source:
--   - generalization: q* = min over Ω of Q(ω) → any q > 0 at most Q(ω) for every ω with Q(ω) > 0; reason: the paper's q* (Q of full support) is such a q; a smaller q only enlarges the right-hand side, and the statement also covers Q without full support
--   - encoding: KL(P∥Q) and the real right-hand side → klDiv P Q ≤ ENNReal.ofReal(right-hand side); reason: Mathlib's KL takes values in [0, ∞]; same instances
--   - encoding: a finite set Ω → a Fintype Ω with Nonempty Ω and a σ-algebra in which singletons are measurable; reason: a probability measure exists only on a nonempty set, and the atoms Q(ω), P(ω) of a measure on a finite set are those of its power-set σ-algebra; no instance is excluded
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 1, p.4 (PDF p.6)

import Mathlib

open MeasureTheory

namespace RGGDetect

/-- **Lemma 1** (Du, Mao, Sun, Wu, Xu, *Sharp detection thresholds for random geometric graphs with
polynomial average degrees*, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 1, p.4):
let `P, Q` be probability measures on a finite set `Ω` with `P ≪ Q`, `Λ = dP/dQ`, and `q* = min Q(ω)`.
Then for every `T ⊆ Ω`,
`KL(P∥Q) ≤ ∫_T (Λ - 1)² dQ + P(Tᶜ) log(1/q*) + Q(Tᶜ)`.

**Formalization Note** `Λ(ω) = P{ω}/Q{ω}`. The bound is stated for every `q > 0` that is at most the
mass of every atom of positive `Q`-mass; `q = min_ω Q(ω)` (full support) is the paper's `q*`, and a
smaller `q` only weakens the right-hand side. -/
theorem lemma_1 {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (qstar : ℝ) (hq : 0 < qstar)
    (hqmin : ∀ ω, 0 < Q.real {ω} → qstar ≤ Q.real {ω}) (T : Finset Ω) :
    InformationTheory.klDiv P Q ≤ ENNReal.ofReal
      (∑ ω ∈ T, (P.real {ω} / Q.real {ω} - 1) ^ 2 * Q.real {ω} +
        P.real (↑T : Set Ω)ᶜ * Real.log (1 / qstar) + Q.real (↑T : Set Ω)ᶜ) := by sorry

end RGGDetect
