-- Prove2me | Theorems.Thm_PottsCIZeroFree_lemma_3_1
-- name    : PottsCIZeroFree.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:25.734083+00:00
-- url     : https://prove2.me/theorems/a091870e-003c-48c8-8532-b30f80f6d972
-- title:
--   Lemma 3.1 — complex averages under nearby laws: $|\mathrm{Log}\,\mathbb E_{\nu_0}[e^{h+\eta}]/\mathbb E_{\nu_1}[e^{h+\eta'}]|\le 2AW_{1,d}(\nu_0,\nu_1)+4\gamma$
-- statement:
--   Let $(\mathcal X,d)$ be a finite metric space, $\nu_0,\nu_1$ probability measures on $\mathcal X$, $A\ge0$ and $\gamma\in[0,1/8]$. Let $h,\eta,\eta':\mathcal X\to\mathbb C$ satisfy
--   1. $|h(\xi)-h(\xi')|\le A\,d(\xi,\xi')$ for all $\xi,\xi'$;
--   2. $\max_{\xi,\xi'}|h(\xi)-h(\xi')|\le 1/8$;
--   3. $\|\eta\|_\infty,\|\eta'\|_\infty\le\gamma$.
--
--   Then $\mathbb E_{\nu_0}[e^{h+\eta}]$ and $\mathbb E_{\nu_1}[e^{h+\eta'}]$ are nonzero and, with the logarithm of their ratio taken as the continuous branch that vanishes at $h=\eta=\eta'=0$ on the convex set of triples satisfying 1–3,
--   $$\left|\operatorname{Log}\frac{\mathbb E_{\nu_0}[e^{h+\eta}]}{\mathbb E_{\nu_1}[e^{h+\eta'}]}\right|\le 2A\,W_{1,d}(\nu_0,\nu_1)+4\gamma .$$
--
--   This stability estimate converts a coupling of two laws into a bound on the change of a logarithmic average; it is the analytic core of the transfer from coupling independence to zero-freeness.
--
--   **Formalization Note** The branch is written through a base point $\xi_*$: for every $\xi_*$, the difference of the principal logarithms of $\mathbb E_{\nu_0}[e^{h-h(\xi_*)+\eta}]$ and $\mathbb E_{\nu_1}[e^{h-h(\xi_*)+\eta'}]$ is bounded. Centering multiplies both averages by the same nonzero factor, both centered averages lie in $\{|w-1|<1\}$, and this difference is continuous on the convex set of admissible triples, vanishes at the origin and exponentiates to the ratio, so it is the branch of the lemma. $W_{1,d}$ is `MarkovMixing.transportDist` with cost $d$; probability measures are nonnegative vectors summing to $1$.
--
--   Differences from the source:
--   - encoding: Log of the ratio as the continuous branch on the convex set of admissible triples vanishing at h = η = η′ = 0 → for every base point ξ*, the difference of the principal logarithms of the two averages centered at h(ξ*); reason: this difference is continuous on the triple set, vanishes at 0 and exponentiates to the ratio, so by uniqueness of continuous logarithms on a connected set it is the branch (the identification made in the proof, p.10)
--   - encoding: probability measures ν₀, ν₁ on a finite metric space → IsDist vectors on a Fintype with a MetricSpace instance; reason: a probability measure on a finite set is its mass vector
-- source:
--   Shao, Shi, Coupling Independence Implies Zero-Freeness, arXiv:2610.12456 (PDF sha256 831a1633…), p.9 (PDF p.11), Lemma 3.1, displays (10)–(13)

import Mathlib
import Definitions.Def_mm_transport

open Classical

namespace PottsCIZeroFree

/-- Lemma 3.1 (Complex averages under nearby laws) of Shao, Shi, *Coupling Independence Implies Zero-Freeness*, arXiv:2610.12456 (PDF sha256 831a1633…), printed p.9 (PDF p.11).
Let `(X, d)` be a finite metric space, `ν₀, ν₁` probability measures on `X`, `A ≥ 0`,
`γ ∈ [0, 1/8]`, and `h, η, η' : X → ℂ` with (10) `|h(ξ) − h(ξ')| ≤ A d(ξ, ξ')`,
(11) `max_{ξ,ξ'} |h(ξ) − h(ξ')| ≤ 1/8`, (12) `‖η‖∞, ‖η'‖∞ ≤ γ`. Then `E_{ν₀}[e^{h+η}]` and
`E_{ν₁}[e^{h+η'}]` are nonzero and, with `Log` of their ratio the continuous branch vanishing
at `h = η = η' = 0` on the convex set of triples satisfying (10)–(12),
`|Log (E_{ν₀}[e^{h+η}] / E_{ν₁}[e^{h+η'}])| ≤ 2A W_{1,d}(ν₀, ν₁) + 4γ` (13).

**Formalization Note.** The branch is written as in the proof (p.9–10): for any base point
`ξ*`, subtracting `h(ξ*)` multiplies both averages by the same nonzero factor, both centered
averages lie in the disc `|w − 1| < 1`, and the difference of their principal logarithms is
continuous on the convex set of admissible triples, vanishes at the origin and exponentiates to
the ratio; so it is the branch of (13). `W_{1,d}` is the published `transportDist` with cost
`dist`. Probability measures are `IsDist` vectors. -/
theorem lemma_3_1 {X : Type*} [Fintype X] [DecidableEq X] [MetricSpace X] (ν₀ ν₁ : X → ℝ)
    (hν₀ : MarkovMixing.IsDist ν₀) (hν₁ : MarkovMixing.IsDist ν₁) (A γ : ℝ) (hA : 0 ≤ A)
    (hγ : γ ∈ Set.Icc (0 : ℝ) (1 / 8)) (h η η' : X → ℂ)
    (h10 : ∀ ξ ξ', ‖h ξ - h ξ'‖ ≤ A * dist ξ ξ')
    (h11 : ∀ ξ ξ', ‖h ξ - h ξ'‖ ≤ 1 / 8)
    (h12 : ∀ ξ, ‖η ξ‖ ≤ γ ∧ ‖η' ξ‖ ≤ γ) :
    (∑ ξ, (ν₀ ξ : ℂ) * Complex.exp (h ξ + η ξ)) ≠ 0 ∧
      (∑ ξ, (ν₁ ξ : ℂ) * Complex.exp (h ξ + η' ξ)) ≠ 0 ∧
      ∀ ξs : X,
        ‖Complex.log (∑ ξ, (ν₀ ξ : ℂ) * Complex.exp (h ξ - h ξs + η ξ)) -
            Complex.log (∑ ξ, (ν₁ ξ : ℂ) * Complex.exp (h ξ - h ξs + η' ξ))‖ ≤
          2 * A * MarkovMixing.transportDist (fun a b => dist a b) ν₀ ν₁ + 4 * γ := by sorry

end PottsCIZeroFree
