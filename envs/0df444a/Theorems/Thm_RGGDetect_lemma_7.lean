-- Prove2me | Theorems.Thm_RGGDetect_lemma_7
-- name    : RGGDetect.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:40:35.322685+00:00
-- url     : https://prove2.me/theorems/987014e6-f890-4d70-bc5f-160355a1d439
-- title:
--   Lemma 7 — Fourier truncation
-- statement:
--   For any fixed integer $K>2/\delta$, with $I=V^c$,
--
--   $$
--   \mathbb E\left[\int_{T_I\cap\{\Lambda_{u,I}\ge1/2\}}\frac{r^2_{u,I,D}}{\Lambda_{u,I}}\,dQ_I\right]\le4\sum_{1\le|S|<K}\mathbb E\big[|\mathbb E[\eta_{D,S}\mid G_{-u}]|^2\big]+o(g(D)), \tag{46}
--   $$
--
--   the sum over $S\subseteq I$.
--
--   On the good-denominator event only the low Fourier levels of the cavity numerator matter.
--
--   **Formalization Note** In the regime (1). $o(g(D))$ is $e_n\,g(D)$ with $e_n\to0$ chosen after the sequences and uniform over every $V$, positive $\boldsymbol\ell$ of even total degree, nonzero $D\in\mathcal H_{\boldsymbol\ell}$ and $u\in V$.
--
--   Differences from the source:
--   - generalization: the standing hypotheses (1) of Theorem 1, for all n → sequences in `Regime δ p d τ`: each hypothesis for all large n; reason: the statement is asymptotic, so sequences satisfying (1) for all n are covered
--   - encoding: o(g(D)) → e_n·g(D) with e → 0 chosen after the sequences, uniform over all V, ℓ, D, u; reason: the paper's asymptotic notation; uniformity is what Proposition 2's supremum uses
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), Lemma 7, eq. (46), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_RGGDetect_Regime
import Definitions.Def_RGGDetect_cavity
import Definitions.Def_RGGDetect_harmPoly

open Filter Topology MeasureTheory

namespace RGGDetect

/-- **Lemma 7** (Fourier truncation; arXiv:2610.08517, held version, sha256 e7bebd4a…, Lemma 7, p.16,
eq. (46)): for any fixed integer `K > 2/δ`,
`E[∫_{T_I ∩ {Λ_{u,I} ≥ 1/2}} r²_{u,I,D}/Λ_{u,I} dQ_I] ≤ 4 ∑_{1 ≤ |S| < K} E[|E[η_{D,S} | G_{-u}]|²] + o(g(D))`,
`I = V^c`, `S ⊆ I`.

**Formalization Note** In the regime (1). The `o(g(D))` is `e_n g(D)` for a sequence `e → 0` chosen
after the sequences and uniform over every `V`, positive multidegree `ℓ` of even total degree,
nonzero `D ∈ H_ℓ` and `u ∈ V` (the standing setting of §3, p.9). -/
theorem lemma_7 (δ : ℝ) (hδ : 0 < δ) (K : ℕ) (hK : (K : ℝ) > 2 / δ) (p : ℕ → ℝ) (d : ℕ → ℕ)
    (τ : ℕ → ℝ) (hR : Regime δ p d τ) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∀ (V : Finset (Fin n)) (ℓ : Fin n → ℕ), (∀ v ∈ V, 1 ≤ ℓ v) → Even (∑ v ∈ V, ℓ v) →
      ∀ D : Config n (d n) → ℝ, D ∈ tensorHarm V ℓ → D ≠ 0 → ∀ u ∈ V,
        cavInt n (d n) (τ n) u Vᶜ D
            (fun g y => y ∈ TI n (capProb (d n) (τ n)) Vᶜ ∧ 1 / 2 ≤ lamUI n (d n) (τ n) u Vᶜ g y) ≤
          4 * ∑ S ∈ (Vᶜ).powerset.filter (fun S => 1 ≤ S.card ∧ S.card < K),
              postMoment (graphMinus (τ n) u) (etaDS (d n) (τ n) D u S) +
            e n * gD (τ n) V ℓ D := by sorry

end RGGDetect
