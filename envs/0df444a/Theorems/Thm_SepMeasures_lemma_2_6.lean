-- Prove2me | Theorems.Thm_SepMeasures_lemma_2_6
-- name    : SepMeasures.lemma_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:52.819943+00:00
-- url     : https://prove2.me/theorems/18c7b395-5082-4147-8605-07d08ba06d6f
-- title:
--   Lemma 2.6 — $|L_{\mu,\nu}-L_{\mu\',\nu\'}|\le W_1(\mu,\mu\')+W_1(\nu,\nu\')$
-- statement:
--   Let $d\ge1$, let $\|\cdot\|$ be a norm on $\mathbb R^d$, and let $\mu,\nu,\mu',\nu'$ be probability measures on $\mathbb R^d$ with finite first moments. With $L_{\mu,\nu}=\int\!\!\int\|x-y\|\,d\mu(x)\,d\nu(y)$ and $W_1$ the 1-Wasserstein distance for the same norm,
--   $$|L_{\mu,\nu}-L_{\mu',\nu'}|\ \le\ W_1(\mu,\mu')+W_1(\nu,\nu').$$
--
--   The lemma is the continuity estimate used whenever a measure is replaced by an approximation (truncation in Lemma 6.1, smoothing in Lemma 6.2).
--
--   **Formalization Note** $W_1$ is valued in $[0,\infty]$; the left side is cast there. $W_1$ is the published optimal transport cost `ShapleyNV.transportCost` with cost $N(x-x')$, over the published couplings `WassersteinDRO.StrongDuality.couplings`.
--
--   Differences from the source:
--   - encoding: a norm ‖·‖ on ℝ^d → N : Seminorm ℝ (EuclideanSpace ℝ (Fin d)) with N x = 0 → x = 0; reason: a definite seminorm is exactly a norm; the Euclidean structure of EuclideanSpace is used only for hyperplane equations, Lebesgue measure, balls and dist(x, H), as in the paper
--   - encoding: finite first moment ∫‖x‖ dµ(x) < ∞ → ∫⁻ x, ENNReal.ofReal (N x) ∂µ < ⊤; reason: the same condition, written as a lower Lebesgue integral
--   - encoding: L_{µ,ν} and C_{µ,ν}(H) as double integrals of ‖x − y‖ → Bochner integrals of N (x − y) over µ.prod ν (restricted to Sep H for C); reason: for pairs with finite first moments the integrand is integrable, so the values are the paper's
--   - encoding: W₁(µ, µ′) = inf over Π(µ, µ′) of ∫∫‖x − x′‖ dπ, compared with the real |L − L′| → W1 in ℝ≥0∞ (ShapleyNV.transportCost with cost N (x − x′)): ⨅ over WassersteinDRO.StrongDuality.couplings of ∫⁻ ofReal (N (x − x′)) dπ, compared with ENNReal.ofReal |L − L′|; reason: no junk values in ℝ≥0∞; for measures with finite first moments W₁ is finite, so the inequality is the paper's
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Lemma 2.6, p.14

import Mathlib
import Definitions.Def_SepMeasures_CutValue
import Definitions.Def_SepMeasures_Families
import Definitions.Def_SepMeasures_W1

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Lemma 2.6, p.14: for every `d ≥ 1`, every norm on
`ℝ^d` and probability measures `μ, ν, μ′, ν′` with finite first moments,
`|L_{μ,ν} − L_{μ′,ν′}| ≤ W₁(μ, μ′) + W₁(ν, ν′)`.

**Formalization Note.** `W₁` takes values in `ℝ≥0∞`, so the left side is cast with
`ENNReal.ofReal`. -/
theorem lemma_2_6 (d : ℕ) (hd : 1 ≤ d) (N : Seminorm ℝ (E d)) (hN : ∀ x, N x = 0 → x = 0)
    (μ ν μ' ν' : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure μ'] [IsProbabilityMeasure ν']
    (hμ : FiniteFirstMoment N μ) (hν : FiniteFirstMoment N ν)
    (hμ' : FiniteFirstMoment N μ') (hν' : FiniteFirstMoment N ν') :
    ENNReal.ofReal |totalDist N μ ν - totalDist N μ' ν'| ≤ W1 N μ μ' + W1 N ν ν' := by sorry

end SepMeasures
