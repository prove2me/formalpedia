-- Prove2me | Theorems.Thm_TentNoise_lemma_A_6
-- name    : TentNoise.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:44:50.906445+00:00
-- url     : https://prove2.me/theorems/98629185-9196-442e-94d8-995616911523
-- title:
--   Lemma A.6 — density ratio bound for the marginals $\mathbb Q^\sigma_t$
-- statement:
--   Let $g:[0,1]\to[0,1]$ be Borel, $\sigma>0$, and let $\mathbb Q^\sigma_t$ be the time-$t$ marginal of the noised fitted path law $\mathbb Q^\sigma_T$ (any horizon $T\ge t$). Then $\mathbb Q^\sigma_t$ has a density $q_t=d\mathbb Q^\sigma_t/d\mu$ for every $t\ge0$, with $q_0=1$. With $M_\sigma$ as in Lemma A.5, for every $t\ge1$,
--
--   $$
--   \mathbb Q^\sigma_t\ll\mu,\qquad \|q_t\|_\infty\le M_\sigma .
--   $$
--
--   Moreover, if $\sigma^2\ge16\,\varepsilon_P$, then
--
--   $$
--   \sup_{t\ge0}\|q_t\|_\infty\le2 .
--   $$
--
--   The noised rollout therefore never concentrates where $g$ may be inaccurate, which transfers the error of $g$ under $\mu$ to the error along the rollout.
--
--   **Formalization Note** The time-$t$ marginal is the push-forward of $\mathbb Q^{g,\sigma}_T$ by coordinate $t\le T$; $q_0=1$ is the statement that the time-$0$ marginal is $\mu$. $\|q_t\|_\infty$ is the $\mu$-essential supremum of the Radon–Nikodym derivative, and $M_\sigma$ is valued in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: g : [0,1] → [0,1] Borel; paths in [0,1]^{T+1} → g : ℝ → ℝ measurable with g([0,1]) ⊆ [0,1]; paths Fin (T+1) → ℝ; reason: every path law is concentrated on [0,1]^{T+1} and values of g off [0,1] are never visited; every Borel map of [0,1] extends to a Borel map of ℝ
--   - encoding: density q_t with ‖q_t‖_∞ ≤ M; q_0 = 1 → ℚ^σ_t ≪ µ and ∀ᵐ y ∂µ, rnDeriv ℚ^σ_t µ y ≤ M; the time-0 marginal equals µ; reason: ‖·‖_∞ of a density is its µ-essential supremum; same content
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma A.6, p.19 (PDF p.19), eqs. (31)–(32)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_errP
import Definitions.Def_TentNoise_Msup

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma A.6 (Density ratio bound for `ℚ^σ_t`)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma A.6, p.19, eqs. (31)–(32)):
let `ℚ^σ_t` be the time-`t` marginal of `ℚ^σ_T` (any horizon `T ≥ t`), `σ > 0`. Then `ℚ^σ_t` has a
density `q_t = dℚ^σ_t/dµ` for every `t ≥ 0`, with `q₀ = 1`; for every `t ≥ 1`, `ℚ^σ_t ≪ µ` and
`‖q_t‖_∞ ≤ M_σ`; and if `σ² ≥ 16 ε_P`, then `sup_{t≥0} ‖q_t‖_∞ ≤ 2`.

**Formalization Note** `g` is any Borel map with `g([0,1]) ⊆ [0,1]` (§2.4). The marginal is the
push-forward of `ℚ^{g,σ}_T` by the coordinate `t ≤ T`; `q₀ = 1` is the statement that the time-0 marginal
is `µ`. `‖q_t‖_∞` is the `µ`-essential supremum of the Radon–Nikodym derivative (`∀ᵐ y ∂µ`). -/
theorem lemma_A_6 (g : ℝ → ℝ) (hg : Measurable g) (hgI : MapsTo g (Icc (0 : ℝ) 1) (Icc 0 1))
    (σ : ℝ) (hσ : 0 < σ) (T : ℕ) :
    (noisedLaw g hg σ T).map (fun p => p 0) = unifI ∧
    (∀ t : Fin (T + 1), 1 ≤ (t : ℕ) →
      (noisedLaw g hg σ T).map (fun p => p t) ≪ unifI ∧
      ∀ᵐ y ∂unifI, ((noisedLaw g hg σ T).map (fun p => p t)).rnDeriv unifI y ≤ Msup σ) ∧
    (16 * errP g ≤ σ ^ 2 → ∀ t : Fin (T + 1),
      ∀ᵐ y ∂unifI, ((noisedLaw g hg σ T).map (fun p => p t)).rnDeriv unifI y ≤ 2) := by sorry

end TentNoise
