-- Prove2me | Theorems.Thm_TentNoise_lemma_B_7
-- name    : TentNoise.lemma_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:55.011421+00:00
-- url     : https://prove2.me/theorems/1904b587-ea46-4718-82e8-2836e84f7641
-- title:
--   Lemma B.7 — small-noise path certificate: $W_{1,\rho_{1,T}}(\mathbb P_T,\mathbb Q^{g,\sigma}_T)\ge b/(16(2+\pi))$
-- statement:
--   Take $N=2^k$, $m=k+1$ and the fitted map $g$ of Lemma B.3 ($0<b\le1/32$). For $T\ge2m$ define
--
--   $$
--   \Phi_T(x):=\frac{1}{(2+\pi)(T-m+1)}\sum_{t=0}^{T-m}\varphi(x_t)\psi(x_{t+m}),\qquad \varphi(x)=x-\tfrac12,\ \psi(x)=\cos(\pi x).
--   $$
--
--   Then $\|\Phi_T\|_\infty\le1$ and $\mathrm{Lip}_{\rho_{1,T}}(\Phi_T)\le1$ on $[0,1]^{T+1}$. Consequently, for $0\le\sigma\le1/(4N)$,
--
--   $$
--   W_{1,\rho_{1,T}}\bigl(\mathbb P_T,\mathbb Q^{g,\sigma}_T\bigr)\ge\frac{b}{16(2+\pi)} .
--   $$
--
--   Averaging the lagged correlation over starting times avoids any loss in $T$, $N$ or $m$.
--
--   **Formalization Note** The sup norm and the Lipschitz constant are over the path space $[0,1]^{T+1}$, the latter with respect to $\rho_{1,T}$.
--
--   Differences from the source:
--   - encoding: the fitted map g of Lemma B.3 with N = 2^k ('From now on take N = 2^k', p.28), a map [0,1] → [0,1]; paths in [0,1]^{T+1} → any g : ℝ → ℝ, measurable, with IsFitMap (2^k) b g (g ∘ h_0 = g ∘ h_1 = id on [0,1]) and 0 < b ≤ 1/32; paths Fin (T+1) → ℝ; reason: IsFitMap pins g down on [0,1] (Lemma B.3) and gives g([0,1]) = [0,1]; values of g off [0,1] are never visited; the paper's g extends to a Borel map of ℝ
--   - encoding: W_{1,ρ_{1,T}} as a real infimum over couplings → the published transport cost with cost ρ_{1,T}, valued in [0,∞], right-hand sides through ENNReal.ofReal; reason: Lean convention; the value is finite for the probability path laws compared, and equal to the paper's
--   - encoding: ‖Φ_T‖_∞ ≤ 1 and Lip_{ρ1,T}(Φ_T) ≤ 1 → |Φ_T x| ≤ 1 and |Φ_T x − Φ_T z| ≤ ρ_{1,T}(x, z) for all x, z ∈ [0,1]^{T+1}; reason: direct transcription on path space
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), Lemma B.7, p.30 (PDF p.30), eqs. (72)–(73)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_pathW1
import Definitions.Def_TentNoise_noisedLaw
import Definitions.Def_TentNoise_IsFitMap
import Definitions.Def_TentNoise_PhiT

open MeasureTheory ProbabilityTheory InformationTheory TeschlODE.Shared Set
open scoped ENNReal NNReal

namespace TentNoise

/-- **Lemma B.7 (A Lipschitz path certificate for small noise)** (Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), Lemma B.7, p.30,
eqs. (72)–(73)): for `T ≥ 2m`, `Φ_T(x) := (1/((2 + π)(T − m + 1))) ∑_{t=0}^{T−m} φ(x_t)ψ(x_{t+m})`
satisfies `‖Φ_T‖_∞ ≤ 1` and `Lip_{ρ_{1,T}}(Φ_T) ≤ 1`; consequently, for `0 ≤ σ ≤ 1/(4N)`,
`W_{1,ρ_{1,T}}(ℙ_T, ℚ^{g,σ}_T) ≥ b/(16(2 + π))`.

**Formalization Note** `N = 2^k`, `m = k + 1`; `g` is Lemma B.3's map (`IsFitMap (2^k) b g`,
`0 < b ≤ 1/32`), Borel on `ℝ`. The sup norm and the Lipschitz constant are over the path space
`[0,1]^{T+1}`, the latter with respect to `ρ_{1,T}`. -/
theorem lemma_B_7 (k : ℕ) (b : ℝ) (hb0 : 0 < b) (hb : b ≤ 1 / 32) (g : ℝ → ℝ) (hg : Measurable g)
    (hfit : IsFitMap (2 ^ k) b g) (T : ℕ) (hT : 2 * (k + 1) ≤ T) :
    (∀ x : Fin (T + 1) → ℝ, (∀ t, x t ∈ Icc (0 : ℝ) 1) → |PhiT T (k + 1) x| ≤ 1) ∧
    (∀ x z : Fin (T + 1) → ℝ, (∀ t, x t ∈ Icc (0 : ℝ) 1) → (∀ t, z t ∈ Icc (0 : ℝ) 1) →
      |PhiT T (k + 1) x - PhiT T (k + 1) z| ≤ pathDist T x z) ∧
    (∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 / (4 * (2 : ℝ) ^ k) →
      ENNReal.ofReal (b / (16 * (2 + Real.pi))) ≤ pathW1 T (trueLaw T) (noisedLaw g hg σ T)) := by sorry

end TentNoise
