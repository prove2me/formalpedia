-- Prove2me | Theorems.Thm_WangZahlKakeya_FSW_card_lower
-- name    : WangZahlKakeya.FSW_card_lower
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T14:46:58.68039+00:00
-- url     : https://prove2.me/theorems/66585d34-f61a-4540-8f48-24088f4404ad
-- title:
--   $C_{\mathrm{F\text{-}SW}}(\mathbb{T})\,(\#\mathbb{T})|T|^{1/2} \gtrsim 1$
-- statement:
--   **The Frostman Slab Wolff constant obeys a universal lower bound.**
--
--   There is an absolute constant $c > 0$ such that every nonempty system $(\mathbb{T},Y)_\delta$ of essentially distinct $\delta$-tubes in the unit ball satisfies
--
--   $$C_{\mathrm{F\text{-}SW}}(\mathbb{T})\,(\#\mathbb{T})\,|T|^{1/2} \;\ge\; c .$$
--
--   The reason, as recorded in the source, is that one can always select a slab $W$ of thickness $|T|^{1/2}$ containing at least one tube of $\mathbb{T}$: taking $W$ to be the intersection of the unit ball with the $|T|^{1/2}$-neighbourhood of the plane through the core line of that tube, the defining inequality $\#\{T \in \mathbb{T} : T \subseteq W\} \le C|W|(\#\mathbb{T})$ applied to $W$ gives $1 \le C|W|(\#\mathbb{T})$, and $|W| \lesssim |T|^{1/2}$.
--
--   **Formalization note.** The source states this with the constant $1$ on the right-hand side; because the volume of a slab of thickness $t$ inside the unit ball is comparable to, but not equal to, $t$, the statement is formalized with an unspecified absolute constant $c > 0$. This quantity is the one that keeps the factor $((\#\mathbb{T})|T|^{1/2})^{-\sigma}$ in Assertion $D(\sigma,\omega)$ from degrading by more than a subpolynomial amount when $\sigma$ is increased.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, p. 6, the discussion following Definition 1.5 (“for every set $\mathbb{T}$ of $\delta$ tubes, we must always have $\mathrm{FS}(\mathbb{T})(\#\mathbb{T})|T|^{1/2}\ge 1$”)

import Definitions.Def_WangZahlKakeya_wolff

namespace WangZahlKakeya

theorem FSW_card_lower :
    ∃ c > (0 : ℝ), ∀ (δ : ℝ) (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      IsTubeSystem δ n p v Y → 0 < n →
      c ≤ FSW δ n p v * ((n : ℝ) * tubeVol δ ^ ((1 : ℝ) / 2)) := by sorry

end WangZahlKakeya
