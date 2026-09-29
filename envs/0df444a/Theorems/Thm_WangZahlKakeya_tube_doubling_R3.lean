-- Prove2me | Theorems.Thm_WangZahlKakeya_tube_doubling_R3
-- name    : WangZahlKakeya.tube_doubling_R3
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T14:16:46.925398+00:00
-- url     : https://prove2.me/theorems/202ae225-3391-4f84-a08b-979a9d9878a9
-- title:
--   Tube doubling conjecture in $\mathbb{R}^3$ (Wang--Zahl, Theorem 1.12)
-- statement:
--   **Doubling a family of tubes increases the volume of its union by at most a subpolynomial factor, in $\mathbb{R}^3$.**
--
--   For a $\delta$-tube $T$ write $\widetilde T$ for its $2$-fold dilate — the tube with the same centre, twice the radius and twice the length. Besicovitch's construction in the plane gives families with $|\bigcup \widetilde T| \gtrsim \frac{\log(1/\delta)}{\log\log(1/\delta)} |\bigcup T|$, and the **Tube Doubling Conjecture** asserts that this logarithmic loss is the worst possible: for every $\varepsilon>0$ and all sufficiently small $\delta>0$, every family $\mathbb{T}$ of $\delta$-tubes satisfies
--
--   $$\Big|\bigcup_{T \in \mathbb{T}} \widetilde T\Big| \;\le\; \delta^{-\varepsilon} \Big|\bigcup_{T\in\mathbb{T}} T\Big| .$$
--
--   The conjecture is classical in dimension two and was open in dimension three; it follows from the endpoint estimates of Theorem 1.9. It is closely related to Keleti's line segment extension conjecture.
--
--   **Formalization Note** The family here is an arbitrary finite indexed family of $\delta$-tubes with unit directions: neither essential distinctness nor containment in the unit ball is assumed, matching the generality of the conjecture as stated in the source.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 15, Theorem 1.12 (Conjecture 1.11 with $n = 3$; proved in §12)

import Definitions.Def_WangZahlKakeya_geometry

namespace WangZahlKakeya
open MeasureTheory Metric Set

theorem tube_doubling_R3 :
    ∀ ε > (0 : ℝ), ∃ δ₀ > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∀ (n : ℕ) (p v : Fin n → E3), (∀ i, ‖v i‖ = 1) →
        (volume (⋃ i, tubeDilate2 (p i) (v i) δ)).toReal ≤
          δ ^ (-ε) * (volume (⋃ i, tube (p i) (v i) δ)).toReal := by sorry

end WangZahlKakeya
