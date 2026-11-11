-- Prove2me | Theorems.Thm_RandProdExp_TwoSided_lemma_6_12
-- name    : RandProdExp.TwoSided.lemma_6_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:21:46.90203+00:00
-- url     : https://prove2.me/theorems/3865657f-1003-4462-8922-9e8ca8e3391b
-- title:
--   Lemma 6.12 — $\|K\|_{\mathrm{op}}<1$ implies that $\tau_M$ is injective (real model)
-- statement:
--   In the random model of Definition 6.2, with $D\ge1$, $n\ge2$, $1\le k_i\le n$ and any fixed signs $\sigma$ (so $G_i=k_i^{-1/2}\sigma^{(i)}$), let $M\subseteq[n]^D$ and let $K$ be its plane-interaction matrix. Then
--   $$\|K\|_{\mathrm{op}}<1\ \Longrightarrow\ \tau_M=\bar\beta^G_M\ \text{is injective}.$$
--   Together with a bound on $\mathbb E\|K\|_{\mathrm{op}}$ it produces injective real instances, the input of the transfer to finite fields.
--
--   Differences from the source:
--   - encoding: standing assumption of §3.1 (p. 19): integers D ≥ 1 and n ≥ 2 → explicit hypotheses 1 ≤ D and 2 ≤ n; reason: stated once at the top of §3.1 for the whole paper; makes the anchor of a plane unique
--   - encoding: the setting of §6 (Definition 6.2: fixed integers 1 ≤ k_i ≤ n, G_i the normalized sign matrices) → explicit hypotheses 1 ≤ k_i ≤ n; the statement holds for every sign tuple σ; reason: the lemma is a deterministic statement about each realization of the model
--   - reading: τ_M for the set M of §6.1–6.2 (no ε-closedness is assumed in Definitions 6.5–6.11) → any M ⊆ [n]^D; reason: neither the lemma nor its proof (Claim 6.14, Lemmas 4.14, 6.6, 6.8) uses ε-closedness
--   - encoding: τ_M = β̄^G_M : Coker α^G_M → U_[D] injective → ker β^G_M ⊆ Im α^G_M (BarInjective); reason: equivalent formulation of injectivity of the induced map
-- source:
--   Chattopadhyay, Ringach, Spooner, Product Expansion of Random Codes via Analytic Techniques, STOC 2027 submission (manuscript sha256 9e4ac2d1…), p. 39, Lemma 6.12

import Mathlib
import Definitions.Def_RandProdExp_TwoSided_Grid
import Definitions.Def_RandProdExp_TwoSided_Diagram
import Definitions.Def_RandProdExp_TwoSided_RealModel

namespace RandProdExp.TwoSided

/-- **Lemma 6.12** (p. 39). In the real random model of Definition 6.2 (`1 ≤ k_i ≤ n`,
`G_i = k_i^{−1/2} σ^{(i)}` for any signs `σ`), if the plane-interaction matrix `K` of `M ⊆ [n]^D`
has `‖K‖_op < 1`, then `τ_M = β̄_M^G` is injective. (Standing assumptions of §3.1: `D ≥ 1`, `n ≥ 2`.) -/
theorem lemma_6_12 (D n : ℕ) (hD : 1 ≤ D) (hn : 2 ≤ n) (k : Fin D → ℕ)
    (hk : ∀ i, 1 ≤ k i ∧ k i ≤ n) (M : Set (Fin D → Fin n)) (σ : SignTuple k n)
    (hK : opNorm (interactionMatrix M σ) < 1) :
    RealTauInjective M σ := by sorry

end RandProdExp.TwoSided
