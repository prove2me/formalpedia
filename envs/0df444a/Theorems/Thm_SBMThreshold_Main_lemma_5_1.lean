-- Prove2me | Theorems.Thm_SBMThreshold_Main_lemma_5_1
-- name    : SBMThreshold.Main.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:48.464977+00:00
-- url     : https://prove2.me/theorems/2b540e16-f2b6-4bd9-b4a3-b80f0438b460
-- title:
--   Lemma 5.1 (m = 1), p. 21 — E[∏_{e∈ζ} W_e | σ_u, σ_v] = σ_uσ_v s^z/n^z for a self-avoiding path or simple cycle ζ
-- statement:
--   Let $0<a<n$ and $0<b<n$, and consider $(\sigma,G)\sim\mathcal G(n,a/n,b/n)$ with $W_e=\mathbf 1_{e\in E(G)}-d/n$, $d=(a+b)/2$, $s=(a-b)/2$. Let $\zeta$ be either a self-avoiding path or a simple cycle, of length $z$, with endpoints $u,v$ ($u=v$ for a cycle). Then for every labelling $\tau$,
--   $$
--   \mathbb E\Bigl[\prod_{e\in\zeta}W_e\Bigm|\sigma_u=\tau_u,\ \sigma_v=\tau_v\Bigr]=\frac{\tau_u\tau_v\,s^z}{n^z}.
--   $$
--
--   The edges of $\zeta$ are distinct, so given the labels their indicators are independent, and each $W_e$ has conditional mean $\pm s/n$. This is the building block of every expected path weight in §5.
--
--   **Formalization Note** This is the case $m=1$ of Lemma 5.1, which holds exactly and needs no asymptotic hypothesis; the case $m\ge2$ is not part of this item. The hypotheses $0<a,b<n$ are Definition 1.1's $q,q'\in(0,1)$. The product over the edges of $\zeta$ is taken over its steps, which cross distinct edges.
-- source:
--   Mossel, Neeman and Sly, A Proof of the Block Model Threshold Conjecture, arXiv:1311.4115v4, p. 21, Lemma 5.1 (case m = 1)

import Mathlib
import Definitions.Def_SBMThreshold_Main_Setting
import Definitions.Def_SBMThreshold_Main_Paths
open Filter Topology Finset

namespace SBMThreshold.Main

/-- Lemma 5.1, case `m = 1` (p. 21): for a self-avoiding path or a simple cycle `ζ` of length `z`
with endpoints `u, v`, `E[∏_{e ∈ ζ} W_e | σ_u, σ_v] = σ_u σ_v s^z / n^z`. -/
theorem lemma_5_1 (n z : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (han : a < n) (hbn : b < n)
    (ζ : Fin (z + 1) → Fin n) (hζ : IsSelfAvoiding ζ ∨ IsSimpleCycle ζ) (τ : Fin n → Bool) :
    condExp n a b {ζ 0, ζ (Fin.last z)} τ (fun _ G => pathX n a b ζ G) =
      spin (τ (ζ 0)) * spin (τ (ζ (Fin.last z))) * sPar a b ^ z / (n : ℝ) ^ z := by sorry

end SBMThreshold.Main
