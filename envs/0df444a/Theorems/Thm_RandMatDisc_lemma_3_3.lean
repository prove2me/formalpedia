-- Prove2me | Theorems.Thm_RandMatDisc_lemma_3_3
-- name    : RandMatDisc.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:48:30.326921+00:00
-- url     : https://prove2.me/theorems/876a57fb-29a7-4a09-8b22-a8cddbf54013
-- title:
--   Lemma 3.3 — robustness of the caps under a Hamming perturbation
-- statement:
--   Let $g_1,\dots,g_N\in\mathbb R^D$, $\xi\in\{\pm1\}^N$, $w_i=\xi_ig_i$, and let $t,p\in\mathbb R$. Suppose the cap event
--
--   $$\inf_{u\in\mathbb S^{D-1}}\#\{i:\langle u,\xi_ig_i\rangle\ge t\}\ \ge\ \frac{pN}2$$
--
--   holds. Then every signing $\sigma\in\{\pm1\}^N$ with Hamming distance $d_H(\sigma,\xi)\le bN$, $b=p/8$, satisfies
--
--   $$\inf_{u\in\mathbb S^{D-1}}\#\{i:\langle u,\sigma_ig_i\rangle\ge t\}\ \ge\ \frac{3pN}8.$$
--
--   The cap property of the initial random signing therefore persists along the whole trajectory of the algorithm as long as it stays near $\xi$.
--
--   Differences from the source:
--   - generalization: the parameters $t,p$ of (13) and the random initial signing $\xi$ → every real $t$, $p$ and every $\xi\in\{\pm1\}^N$, $g$ fixed; reason: the paper notes the lemma is deterministic on the event (14) (p.17); the paper's $t,p,\xi$ are one instance
--   - encoding: signs $\sigma\in\{-1,1\}^N$ → real vectors with entries $\pm1$; reason: Lean convention; same signings
--   - encoding: $\inf_u$ of a count → the bound for every unit vector $u$; reason: equivalent for counts
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (held file sha256 889af7fc…), Lemma 3.3, p.17 (PDF p.19), eq. (17)

import Definitions.Def_RandMatDisc_capCount

namespace RandMatDisc

/-- **Lemma 3.3 (Robustness under a Hamming perturbation)**, Kızıldağ, Li, arXiv:2610.01591
(held file sha256 889af7fc…), p.17 (PDF p.19).

Let `ξ ∈ {±1}ᴺ` and `wᵢ = ξᵢ gᵢ`. On the event (14),
`inf_{u ∈ S^{D−1}} #{i : ⟨u, ξᵢ gᵢ⟩ ≥ t} ≥ pN/2`, every signing `σ ∈ {±1}ᴺ` with
`d_H(σ, ξ) ≤ bN`, `b = p/8`, satisfies `inf_{u ∈ S^{D−1}} #{i : ⟨u, σᵢ gᵢ⟩ ≥ t} ≥ 3pN/8` (17).

**Formalization Note.** The lemma is deterministic on the event (the paper, p.17: "On the 'cap
event' (14), Lemma 3.3 is deterministic"), so it is stated for every realization of `g` and `ξ`
and for every real `t` and `p` (the paper's are those of (13)). `d_H` is `hammingDist`. -/
theorem lemma_3_3 {D N : ℕ} (g : Fin N → EuclideanSpace ℝ (Fin D)) (ξ : Fin N → ℝ) (t p : ℝ)
    (hξ : ∀ i, ξ i = 1 ∨ ξ i = -1)
    (hcap : ∀ u : EuclideanSpace ℝ (Fin D), ‖u‖ = 1 →
      p * N / 2 ≤ (capCount u (fun i => ξ i • g i) t : ℝ)) :
    ∀ σ : Fin N → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) → (hammingDist σ ξ : ℝ) ≤ p / 8 * N →
      ∀ u : EuclideanSpace ℝ (Fin D), ‖u‖ = 1 →
        3 * p * N / 8 ≤ (capCount u (fun i => σ i • g i) t : ℝ) := by sorry

end RandMatDisc
