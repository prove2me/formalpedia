-- Prove2me | Theorems.Thm_PreservePast_theorem_1
-- name    : PreservePast.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:19.976378+00:00
-- url     : https://prove2.me/theorems/443956a4-0a63-4a60-9107-2e5ca014f900
-- title:
--   Theorem 1 — from shared-response deficit to compatible prior mass
-- statement:
--   Let histories carry a prior probability $\mu$, let $g_h(z)$ be a score with finite values $V(h)=\sup_zg_h(z)$, let $\mathcal T$ be a domain of histories, $n\ge1$ and $b\ge0$, and assume the scores, the values and the event $W_n(b)$ are measurable. Let $E_a$ be a measurable set of histories (those compatible with a response $a$). If there are a measurable $E_a'\subseteq E_a\cap\mathcal T$ with $\mu(E_a')\ge\kappa\mu(E_a)$, $0<\kappa\le1$, and a single action $z_a$ with $V(h)-g_h(z_a)\le b$ for all $h\in E_a'$, then
--   $$
--   \mu(E_a)\le\kappa^{-1}\exp\{-\mathcal H_n(b;\mu)\}.
--   $$
--
--   The theorem turns the source exponent into a bound on the prior mass of histories that one response can serve, the first step of every lower bound in the paper.
--
--   **Formalization Note** "Finite values" is boundedness above of each $z\mapsto g_h(z)$. The inequality is in $[0,\infty]$, with $\exp(-\infty)=0$ when $\mu^n(W_n(b))=0$.
--
--   Differences from the source:
--   - encoding: scores and values finite → each z ↦ g_h(z) bounded above (real-valued scores); reason: the same condition; V(h) is then a real supremum
--   - encoding: 𝓗_n real-valued, −ln 0 → extended-real 𝓗_n with −ln 0 = +∞, exp(−∞) = 0; reason: the source's convention made explicit; same instances
--   - generalization: E_a the measurable set of histories compatible with a response a → an arbitrary measurable set E with the stated E′, κ and z_a; reason: compatibility enters the theorem only through these hypotheses; the source's compatible set is one instance
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §1.2.1, p.2 (PDF p.4), Theorem 1

import Mathlib
import Definitions.Def_PreservePast_sourceExp

open MeasureTheory

namespace PreservePast

/-- **Theorem 1 (from shared-response deficit to compatible prior mass).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §1.2.1, p.2
(PDF p.4): "Assume the scores and values are finite and measurable and the events above are
measurable. Let E_a be the measurable set of histories compatible with a response a. Suppose there
exists a measurable subset E′_a ⊆ E_a ∩ 𝒯 with µ(E′_a) ≥ κµ(E_a) (0 < κ ≤ 1) and a single action
z_a ∈ 𝓑 such that V(h) − g_h(z_a) ≤ b for all h ∈ E′_a. Then µ(E_a) ≤ κ^{−1} exp{−𝓗_n(b; µ)}."

Histories live in a measurable space `Θ` with prior `µ`, actions in `𝓑`, `g_h(z)` is the score,
`V(h) = sup_z g_h(z)` (`optVal`), `𝒯` the domain of histories, `n ≥ 1`, `b ≥ 0`.

**Formalization Note.** "Finite values" is `BddAbove` of each `z ↦ g_h(z)`; "the events above are
measurable" is the measurability of `W_n(b)`. The conclusion is in `ℝ≥0∞` with `exp(−(+∞)) = 0`. -/
theorem theorem_1 {Θ 𝓑 : Type*} [MeasurableSpace Θ] (μ : Measure Θ) [IsProbabilityMeasure μ]
    (g : Θ → 𝓑 → ℝ) (𝒯 : Set Θ) (n : ℕ) (hn : 1 ≤ n) (b : ℝ) (hb : 0 ≤ b)
    (hfin : ∀ h, BddAbove (Set.range (g h))) (hgm : ∀ z, Measurable (fun h => g h z))
    (hVm : Measurable (optVal g)) (hW : MeasurableSet (Wset g 𝒯 n b))
    (E E' : Set Θ) (hE : MeasurableSet E) (hE' : MeasurableSet E') (hsub : E' ⊆ E ∩ 𝒯)
    (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hmass : ENNReal.ofReal κ * μ E ≤ μ E')
    (za : 𝓑) (hza : ∀ h ∈ E', optVal g h - g h za ≤ b) :
    μ E ≤ ENNReal.ofReal κ⁻¹ * EReal.exp (-sourceExp g 𝒯 μ n b) := by sorry

end PreservePast
