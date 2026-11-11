-- Prove2me | Theorems.Thm_SensLabelCover_DH_lemma_3_4
-- name    : SensLabelCover.DH.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:35:35.555212+00:00
-- url     : https://prove2.me/theorems/9f7cab7d-77ea-4cdc-9a65-5c2dbc610eb5
-- title:
--   Lemma 3.4 — composing recoveries: $C^+_{\mathcal T}\le C_{\mathcal T}t$, $C^+_{\mathcal R}\le C_{\mathcal R}r$, $D^+_{\mathcal R}\le D_{\mathcal R}+C_{\mathcal T}C_{\mathcal R}d$
-- statement:
--   Let $\Phi\mapsto\mathcal T(\Phi)$ have recoveries $\mathcal R_\Phi$ on distributions with sensitivity-transfer parameters $(C_{\mathcal T},C_{\mathcal R},D_{\mathcal R})$ on a source family $\mathcal X$. Let $\mathcal J$ be a swap-closed family containing every $\mathcal T(\Phi)$, $\Phi\in\mathcal X$, and let $\mathcal T_{step}$ be a further transformation with a pointwise recovery $R_I$ (an output of $\mathcal T_{step}(I)$ to a distribution on outputs of $I$) for each $I\in\mathcal J$. Suppose that for all neighbouring $I,\tilde I\in\mathcal J$,
--   $$\mathrm{SwapDist}(\mathcal T_{step}(I),\mathcal T_{step}(\tilde I))\le t,\qquad \mathrm{EMD}(R_I(y),R_{\tilde I}(y))\le d\ \text{ for every }y,$$
--   and that $\mathrm{EMD}(R_I(y),R_I(\tilde y))\le r\,d_H(y,\tilde y)$ for every $I\in\mathcal J$ and all $y,\tilde y$. Define $\mathcal R^+_\Phi(\mu)=\mathcal R_\Phi((R_{\mathcal T(\Phi)})_\#\mu)$. Then $\mathcal T_{step}\circ\mathcal T$ with recoveries $\mathcal R^+_\Phi$ has sensitivity-transfer parameters
--   $$C^+_{\mathcal T}\le C_{\mathcal T}\,t,\qquad C^+_{\mathcal R}\le C_{\mathcal R}\,r,\qquad D^+_{\mathcal R}\le D_{\mathcal R}+C_{\mathcal T}C_{\mathcal R}\,d .$$
--
--   This is the composition rule the paper uses to accumulate transfer losses over its iterated reductions.
--
--   Differences from the source:
--   - generalization: Hamming distances on source, intermediate and final outputs → pseudometric costs $d_X,d_Y$ and an arbitrary cost $d_Z$; reason: Hamming distances are pseudometrics, so the statement specializes to the paper's.
--   - reading: transfer parameters and the bounds $t,r,d$ → nonnegative reals; reason: they bound nonnegative quantities (swap counts, Lipschitz constants, EMDs).
--   - encoding: instances, swap relations and output spaces → abstract types with one output type per problem (so "a common range" is automatic); the conclusion "the composed map has parameters satisfying …" → the triple $(C_{\mathcal T}t,\,C_{\mathcal R}r,\,D_{\mathcal R}+C_{\mathcal T}C_{\mathcal R}d)$ is a parameter triple; reason: parameters are upper bounds, so these are the same statement.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 20 (PDF 23), setup paragraph and Lemma 3.4

import Mathlib
import Definitions.Def_SensLabelCover_DH_Sensitivity

namespace SensLabelCover.DH

/-- Lemma 3.4 (Composing recoveries), p. 20 (PDF p. 23), with the setup paragraph before it.
`𝒯 : S → T` with recovery `ℛ` on distributions has parameters `(C_𝒯, C_ℛ, D_ℛ)` on the source
family `𝓧`; `𝓙` is a swap-closed family containing every `𝒯(Φ)`; `𝒯step : T → T₂` has pointwise
recoveries `R I : Z → D(Y)` with bounds `t, r, d`. The composed transformation `𝒯step ∘ 𝒯` with
`ℛ⁺_Φ(μ) := ℛ_Φ((R_{𝒯(Φ)})_#μ)` has parameters `(C_𝒯 t, C_ℛ r, D_ℛ + C_𝒯 C_ℛ d)`. -/
theorem lemma_3_4 {S T T₂ OX OY OZ : Type} [Fintype OX] [Fintype OY] [Fintype OZ]
    (adjS : S → S → Prop) (adjT : T → T → Prop) (adjT₂ : T₂ → T₂ → Prop)
    (dX : OX → OX → ℝ) (dY : OY → OY → ℝ) (dZ : OZ → OZ → ℝ)
    (hdX : IsPseudoCost dX) (hdY : IsPseudoCost dY)
    (𝓧 : Set S) (𝒯 : S → T) (ℛ : S → PMF OY → PMF OX) (CT CR DR : ℝ)
    (hpar : IsTransferParams adjS adjT dX dY 𝓧 𝒯 ℛ CT CR DR)
    (𝓙 : Set T) (h𝓙 : SwapClosed adjT 𝓙) (h𝒯𝓙 : ∀ Φ ∈ 𝓧, 𝒯 Φ ∈ 𝓙)
    (𝒯step : T → T₂) (R : T → OZ → PMF OY) (t r d : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) (hd : 0 ≤ d)
    (hstep : ∀ I ∈ 𝓙, ∀ J ∈ 𝓙, adjT I J → SwapDistLE adjT₂ (𝒯step I) (𝒯step J) t)
    (hrule : ∀ I ∈ 𝓙, ∀ J ∈ 𝓙, adjT I J → ∀ y : OZ, emd dY (R I y) (R J y) ≤ d)
    (hLip : ∀ I ∈ 𝓙, ∀ y y' : OZ, emd dY (R I y) (R I y') ≤ r * dZ y y') :
    IsTransferParams adjS adjT₂ dX dZ 𝓧 (fun Φ => 𝒯step (𝒯 Φ))
      (fun Φ μ => ℛ Φ (μ.bind (R (𝒯 Φ)))) (CT * t) (CR * r) (DR + CT * CR * d) := by sorry

end SensLabelCover.DH
