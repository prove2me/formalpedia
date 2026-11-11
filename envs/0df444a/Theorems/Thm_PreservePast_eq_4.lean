-- Prove2me | Theorems.Thm_PreservePast_eq_4
-- name    : PreservePast.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:18.284378+00:00
-- url     : https://prove2.me/theorems/36357dd6-f0b8-445d-bd47-ebdf728c3519
-- title:
--   (4) — Theorem 1 combined with Lemma 1: $B\ge\frac{s_0}{\ln2}(\mathcal H_n(b;\mu)-\ln(1/\kappa))_+-1$
-- statement:
--   Let the history $H\sim\mu$ be independent of the public randomness $\mathcal U$, let $M$ be a $B$-bit message (an arbitrary random variable with at most $2^B$ values), and let the decoder's response be $a=\mathrm{dec}(M,\mathcal U)$. Suppose every response $a$ has a measurable compatible set $E_a$ satisfying the hypotheses of Theorem 1 with common $\kappa\in(0,1]$, $b\ge0$ and $n\ge1$: a measurable $E_a'\subseteq E_a\cap\mathcal T$ with $\mu(E_a')\ge\kappa\mu(E_a)$ and an action $z_a$ with $V(h)-g_h(z_a)\le b$ on $E_a'$. Let $s_0=\Pr\{H\in E_{\mathrm{dec}(M,\mathcal U)}\}$ be the probability that the actual history belongs to its selected compatible set. Then
--   $$
--   B\ \ge\ \frac{s_0}{\ln2}\big(\mathcal H_n(b;\mu)-\ln(1/\kappa)\big)_+-1,\qquad (x)_+=\max\{x,0\}.
--   $$
--
--   This is the bit lower bound used for every converse of the paper.
--
--   **Formalization Note** In the extended reals ($\mathcal H_n$ may be $+\infty$). The decoder's coins are part of $\mathcal U$. The selection $\{(h,u):h\in E_{\mathrm{dec}(m,u)}\}$ is assumed measurable for each message $m$, so that $s_0$ is the probability of an event.
--
--   Differences from the source:
--   - encoding: the response of the decoder (with its own coins) → a = dec(M, 𝒰), the decoder's coins being part of 𝒰; reason: same instances
--   - encoding: s₀ the probability of membership in the selected compatible set → joint measurability of {(h, u) : h ∈ E_{dec(m,u)}} for each message m; reason: needed for s₀ to be the probability of an event; the source assumes the events measurable
--   - generalization: the selected compatible sets E_a (histories compatible with response a) → an arbitrary measurable family E_a satisfying Theorem 1's hypotheses with common κ, b, n for every response a; reason: compatibility enters (4) only through Theorem 1's hypotheses; the source's compatible sets are one instance
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §1.2.1, p.3 (PDF p.5), (4)

import Mathlib
import Definitions.Def_PreservePast_sourceExp

open MeasureTheory ProbabilityTheory

namespace PreservePast

/-- **(4): Theorem 1 combined with Lemma 1.** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §1.2.1, p.3 (PDF p.5): "Combining Theorem 1
with Lemma 1 immediately gives B ≥ (s₀/ln 2)(𝓗_n(b; µ) − ln(1/κ))₊ − 1 (4), where (x)₊ = max{x, 0}
and s₀ is the probability that the actual history belongs to its selected compatible set."

Setting: the history `H ∼ µ` is independent of the public randomness `𝒰`; the `B`-bit message
`M` is an arbitrary random variable (jointly randomized); the response is `a = dec(M, 𝒰)`
(decoder coins are part of `𝒰`). Every response `a` has a measurable compatible set `E_a` satisfying
the hypotheses of Theorem 1 with the same `κ, b, n`: a measurable `E′_a ⊆ E_a ∩ 𝒯` with
`µ(E′_a) ≥ κµ(E_a)` and an action `z_a` with `V(h) − g_h(z_a) ≤ b` on `E′_a`.
`s₀ = Pr{H ∈ E_{dec(M,𝒰)}}`.

**Formalization Note.** In `EReal` (`𝓗_n` may be `+∞`). Measurability of the selection:
`{(h, u) : h ∈ E_{dec(m,u)}}` is measurable for every message `m`. -/
theorem eq_4 {Ω Θ 𝓑 𝒰 𝒜 : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace 𝒰]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure Θ) [IsProbabilityMeasure μ]
    (g : Θ → 𝓑 → ℝ) (𝒯 : Set Θ) (n : ℕ) (hn : 1 ≤ n) (b : ℝ) (hb : 0 ≤ b)
    (hfin : ∀ h, BddAbove (Set.range (g h))) (hgm : ∀ z, Measurable (fun h => g h z))
    (hVm : Measurable (optVal g)) (hW : MeasurableSet (Wset g 𝒯 n b))
    (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (B : ℕ) (H : Ω → Θ) (U : Ω → 𝒰) (M : Ω → Fin (2 ^ B))
    (hH : Measurable H) (hU : Measurable U) (hM : Measurable M) (hlaw : P.map H = μ)
    (hind : IndepFun H U P)
    (dec : Fin (2 ^ B) → 𝒰 → 𝒜) (E E' : 𝒜 → Set Θ) (za : 𝒜 → 𝓑)
    (hEsel : ∀ m, MeasurableSet {q : Θ × 𝒰 | q.1 ∈ E (dec m q.2)})
    (hE : ∀ a, MeasurableSet (E a)) (hE' : ∀ a, MeasurableSet (E' a))
    (hsub : ∀ a, E' a ⊆ E a ∩ 𝒯) (hmass : ∀ a, ENNReal.ofReal κ * μ (E a) ≤ μ (E' a))
    (hza : ∀ a, ∀ h ∈ E' a, optVal g h - g h (za a) ≤ b) :
    let s₀ : ℝ := (P {ω | H ω ∈ E (dec (M ω) (U ω))}).toReal
    ((s₀ / Real.log 2 : ℝ) : EReal) *
        max (sourceExp g 𝒯 μ n b - ((Real.log (1 / κ) : ℝ) : EReal)) 0 - 1 ≤ (B : EReal) := by sorry

end PreservePast
