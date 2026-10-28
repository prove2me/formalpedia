-- Prove2me | Theorems.Thm_ThresholdTheorem_weight_le_of_disjoint_pair_witness
-- name    : ThresholdTheorem.weight_le_of_disjoint_pair_witness
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T20:45:35.941967+00:00
-- url     : https://prove2.me/theorems/4d229c5d-f26e-4b22-bfe1-a9fba111e5c3
-- title:
--   Disjoint pair witnesses turn local stochastic rate $e$ into rate $Me^2$
-- statement:
--   **Probability bound from disjoint pair witnesses.** Let $w_1,\dots,w_r\ge0$ be weights and $F_1,\dots,F_r$ finite sets of locations. Think of them as a finite random fault set $F$ with $\Pr[F=F_i]=w_i$, and assume it is *local stochastic* with rate $e\ge0$:
--   $$\sum_{i\,:\,S\subseteq F_i} w_i\le e^{|S|}\qquad\text{for every finite set }S.$$
--   Let $\Phi$ map sets of locations to sets of locations. For every location $\ell$, let $\mathrm{pairs}(\ell)$ be a family of at most $M$ two-element sets. Assume the *disjoint witness* property: whenever $S\subseteq\Phi(G)$, one can pick $g(\ell)\in\mathrm{pairs}(\ell)$ with $g(\ell)\subseteq G$ for each $\ell\in S$, the chosen pairs being pairwise disjoint. Then the image fault set $\Phi(F)$ is local stochastic with rate $Me^2$:
--   $$\sum_{i\,:\,S\subseteq\Phi(F_i)} w_i\le (M e^2)^{|S|}\qquad\text{for every finite set }S.$$
--
--   Proof: if $S\subseteq\Phi(F_i)$, some choice function $g\in\prod_{\ell\in S}\mathrm{pairs}(\ell)$ has pairwise disjoint values contained in $F_i$, so their union $U_g$ (of size $2|S|$) is contained in $F_i$. A union bound over the at most $M^{|S|}$ choice functions gives
--   $$\sum_{i:S\subseteq\Phi(F_i)}w_i\le\sum_{g}\ \sum_{i:U_g\subseteq F_i}w_i\le M^{|S|}e^{2|S|}.$$
--   This is the counting step of the level reduction for local stochastic noise.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, arXiv:quant-ph/0504218, Sec. 5 (counting of bad exRecs under local stochastic noise: each bad exRec is charged a disjoint pair of faults); D. Gottesman, arXiv:0904.2557, Sec. 5.

import Mathlib

namespace ThresholdTheorem
theorem weight_le_of_disjoint_pair_witness {r : ℕ} (w : Fin r → ℝ)
    (F : Fin r → Finset (ℕ × ℕ)) (e : ℝ) (he : 0 ≤ e) (hw : ∀ i, 0 ≤ w i)
    (hF : ∀ S : Finset (ℕ × ℕ),
      ∑ i ∈ Finset.univ.filter (fun i => S ⊆ F i), w i ≤ e ^ S.card)
    (M : ℕ) (pairs : ℕ × ℕ → Finset (Finset (ℕ × ℕ)))
    (Φ : Finset (ℕ × ℕ) → Finset (ℕ × ℕ))
    (hcard : ∀ ℓ, (pairs ℓ).card ≤ M) (htwo : ∀ ℓ, ∀ p ∈ pairs ℓ, p.card = 2)
    (hwit : ∀ (G S : Finset (ℕ × ℕ)), S ⊆ Φ G →
      ∃ g : ℕ × ℕ → Finset (ℕ × ℕ), (∀ ℓ ∈ S, g ℓ ∈ pairs ℓ ∧ g ℓ ⊆ G) ∧
        ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ℓ₁ ≠ ℓ₂ → Disjoint (g ℓ₁) (g ℓ₂))
    (S : Finset (ℕ × ℕ)) :
    ∑ i ∈ Finset.univ.filter (fun i => S ⊆ Φ (F i)), w i ≤ ((M : ℝ) * e ^ 2) ^ S.card := by sorry
end ThresholdTheorem
