-- Prove2me | Theorems.Thm_TractableDRO_Unified_theorem_4
-- name    : TractableDRO.Unified.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:13:44.216492+00:00
-- url     : https://prove2.me/theorems/59e9b4f3-2697-414d-997d-a81df3057ff9
-- title:
--   Theorem 4, p. 911 — sup over ⋂_{s∈S} 𝔽_s of E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π(r⁰, r) ≤ π^s(r⁰, r) for all s ∈ S
-- statement:
--   Let $\mathcal V,\hat{\mathcal V}\subseteq\mathbb R^{N_E}$, $F\in\mathbb R^{N\times N_E}$, $\Sigma\in\mathbb R^{N\times N}$, $F_\sigma\in\mathbb R^{N_\sigma\times N_E}$, $g_\sigma\in\mathbb R^{N_\sigma}$, $\hat{\mathcal W}_\sigma\subseteq\mathbb R^{N_\sigma}$ and $\sigma_f,\sigma_b\in\mathbb R^{N_\sigma}$ be the data of the model, with $\sigma_f\ge0$, $\sigma_b\ge0$ and $F_\sigma\hat\zeta+g_\sigma\in\hat{\mathcal W}_\sigma$ for every $\hat\zeta\in\hat{\mathcal V}$. Let $\mathbb F_1,\mathbb F_2,\mathbb F_3$ be the families of distributions of Theorems 1–3 and $\pi^1,\pi^2,\pi^3$ the bounds (21), (22), (24). Let $S\subseteq\{1,2,3\}$ be an index set of the bounds to be combined, $\mathbb F=\bigcap_{s\in S}\mathbb F_s$, and
--   $$\pi(r^0,r)=\min\Big\{\sum_{s\in S}\pi^s(r^{0,s},r^s):\ r^0=\sum_{s\in S}r^{0,s},\ r=\sum_{s\in S}r^s\Big\}.\quad(25)$$
--   Then for every $r^0\in\mathbb R$ and $r\in\mathbb R^{N_E}$,
--   $$\sup_{\mathbb P\in\mathbb F}E_{\mathbb P}\big((r^0+r'\tilde\zeta)^+\big)\le\pi(r^0,r)\le\pi^s(r^0,r)\qquad\forall s\in S.\quad(26)$$
--
--   This is Theorem 4 of Goh and Sim: when the true distribution is known to satisfy several of the three kinds of partial information at once, the infimal convolution of the separate bounds is a valid bound for the intersected family and is at least as good as each separate bound. It is the bound used in §6 for the deflected linear decision rules.
--
--   **Formalization Note** Values are in `EReal`, with $\sup\emptyset=-\infty$ and $\inf\emptyset=+\infty$ (p. 909); the "min" of (25) is read as an infimum. $S$ is a `Finset (Fin 3)` with index $0,1,2$ standing for the paper's $1,2,3$; no nonemptiness is imposed (for $S=\emptyset$ the bound $\pi$ is $0$ at $(0,0)$ and $+\infty$ elsewhere, so (26) holds trivially). The hypotheses $\sigma_f,\sigma_b\ge0$ and the inclusion are those of Theorem 3 (see there for their source in the paper's model, pp. 905, 908, 910); they are stated for all $S$ and are harmless when $3\notin S$.
-- source:
--   Goh & Sim, Distributionally Robust Optimization and Its Tractable Approximations, Oper. Res. 58(4), 2010, p. 911, Theorem 4, (25), (26)

import Mathlib
import Definitions.Def_TractableDRO_Unified_Model

open MeasureTheory ProbabilityTheory Matrix

namespace TractableDRO.Unified

/-- Theorem 4, p. 911, (26): for `S ⊆ {1, 2, 3}` and `𝔽 = ⋂_{s∈S} 𝔽_s`,
`sup_{ℙ∈𝔽} E_ℙ((r⁰ + r′ζ̃)⁺) ≤ π(r⁰, r) ≤ π^s(r⁰, r)` for all `s ∈ S`. -/
theorem theorem_4 {n N Nσ : ℕ} (D : Data n N Nσ) (S : Finset (Fin 3))
    (hσf : 0 ≤ D.σf) (hσb : 0 ≤ D.σb) (hW : ∀ ζh ∈ D.Vhat, D.Fσ *ᵥ ζh + D.gσ ∈ D.Wσhat)
    (r0 : ℝ) (r : Fin n → ℝ) :
    TractableDRO.MeanSupport.worstCase (familyU D S) r0 r ≤ piU D S r0 r ∧ ∀ s ∈ S, piU D S r0 r ≤ piOf D s r0 r := by sorry

end TractableDRO.Unified
