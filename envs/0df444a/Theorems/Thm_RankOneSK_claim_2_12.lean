-- Prove2me | Theorems.Thm_RankOneSK_claim_2_12
-- name    : RankOneSK.claim_2_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:30:18.666719+00:00
-- url     : https://prove2.me/theorems/df3364d7-5769-4d0a-aff2-b8018ab0d125
-- title:
--   Claim 2.12 — $\mathbb E\sup_{z\in S^{n-1}}(\frac{2\beta}{\sqrt n}g^\top z-\rho\|z\|^2_{\le\delta n})\le2\beta-\frac{\pi\beta\rho}{6(\beta+\rho)}\delta^3+\frac{\pi\beta\rho\delta^2}{2n(\beta+\rho)}$
-- statement:
--   Let $n\ge1$, $\delta\in(0,1)$, $\rho,\beta>0$, let $g\sim\mathcal N(0,I_n)$ be a standard Gaussian vector and $S^{n-1}=\{z\in\mathbb R^n:\|z\|_2=1\}$. Let $\|z\|^2_{\le\delta n}$ be the sum of the $\lfloor\delta n\rfloor$ smallest squared coordinates of $z$.
--
--   **Claim 2.12.** The supremum below is integrable, and
--   $$\mathbb E\sup_{z\in S^{n-1}}\Big(\frac{2\beta}{\sqrt n}g^\top z-\rho\|z\|^2_{\le\delta n}\Big)\ \le\ 2\beta-\frac{\pi\beta\rho}{6(\beta+\rho)}\delta^3+\frac{\pi\beta\rho\,\delta^2}{2n(\beta+\rho)} .$$
--
--   This bounds the comparison process in the proof of Lemma 2.10; the gain $\frac{\pi\beta\rho}{6(\beta+\rho)}\delta^3$ below $2\beta$ is what forces near-top eigenvectors of $J$ to be delocalized.
--
--   Differences from the source:
--   - encoding: δ ∈ (0, 1), ρ, β > 0, g ∼ N(0, I_n) from the setting of Lemma 2.10 and its proof → explicit hypotheses; g with law Measure.pi (fun _ => gaussianReal 0 1); reason: context of the claim
--   - encoding: n (implicitly ⩾ 1) → 1 ⩽ n; reason: for n = 0 the sphere is empty and the right side divides by 0: the excluded case is undefined in the source
--   - encoding: E sup over S^{n−1} → integrability of the real supremum over {z : Σ z_i² = 1} is part of the conclusion, and the bound is on its Bochner integral; reason: the supremum is bounded by (2β/√n)∥g∥₂, so it is integrable; stating it rules out a junk integral
--   - encoding: ∥z∥²_{⩽δn} → smallSumSq z (δ n); reason: same quantity for δ ∈ (0, 1)
-- source:
--   Boban, Li & Oveis Gharan, Rank-1-perturbed trickledown theorems, arXiv:2609.13138, Claim 2.12, p.16 (PDF p.17), in the setting of Lemma 2.10, p.15

import Mathlib
import Definitions.Def_RankOneSK_smallSumSq

open MeasureTheory ProbabilityTheory Real

namespace RankOneSK

/-- **Claim 2.12.** For `δ ∈ (0, 1)`, `ρ, β > 0` and `g ∼ N(0, I_n)`,
`E sup_{z∈S^{n−1}} ((2β/√n) gᵀz − ρ∥z∥²_{⩽δn}) ⩽ 2β − (πβρ/(6(β + ρ)))δ³ + πβρδ²/(2n(β + ρ))`.

Boban, Li & Oveis Gharan, *Rank-1-perturbed trickledown theorems*, arXiv:2609.13138, Claim 2.12, p.16, in the setting of Lemma 2.10, p.15 (`δ ∈ (0, 1)`, `ρ, β > 0`) and its proof
(`g ∼ N(0, I_n)`).

**Formalization Note** `n ⩾ 1`, so that the unit sphere `S^{n−1} = {z : Σ_i z_i² = 1}` is nonempty. `g` has
law `Measure.pi (fun _ => gaussianReal 0 1)`. The supremum is a real `⨆` over the sphere, which is bounded
for every `g`; integrability of the supremum is part of the conclusion (so the Bochner integral is not a
junk value). `∥z∥²_{⩽δn}` is `smallSumSq z (δ n)`. The bound holds for every `n ⩾ 1`. -/
theorem claim_2_12 (n : ℕ) (hn : 1 ≤ n) (δ ρ β : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hρ : 0 < ρ)
    (hβ : 0 < β) :
    let S : (Fin n → ℝ) → ℝ := fun g =>
      ⨆ z : {z : Fin n → ℝ // ∑ i, z i ^ 2 = 1},
        2 * β / Real.sqrt n * ∑ i, g i * z.1 i - ρ * smallSumSq z.1 (δ * n)
    Integrable S (Measure.pi fun _ : Fin n => gaussianReal 0 1) ∧
      ∫ g, S g ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) ≤
        2 * β - π * β * ρ / (6 * (β + ρ)) * δ ^ 3 + π * β * ρ * δ ^ 2 / (2 * n * (β + ρ)) := by sorry

end RankOneSK
