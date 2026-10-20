-- Prove2me | Theorems.Thm_SharingPlatform_WageSchemes_lemma_1
-- name    : SharingPlatform.WageSchemes.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:58.940409+00:00
-- url     : https://prove2.me/theorems/1da03184-1159-4b1b-b430-bbab0289ce48
-- title:
--   Lemma 1, p. 10 (PDF 11) — the DCR symmetric equilibrium: price (4) and commission rate (5)
-- statement:
--   Consider the dynamic-commission-rate game, in which two platforms simultaneously choose a consumer price $p_i$ and a commission rate $\alpha_i$, demand is $d_i = a - b(p_i - p_{\bar i}) - c p_i$, supply is $s_i = -k + l(w_i - w_{\bar i}) + m w_i$ with $w_i = (1-\alpha_i)p_i$, and profit is $\alpha_i p_i \max\{0,\min\{d_i,s_i\}\}$. Assume $a,b,c,k,l,m > 0$, $a/c > k/m$ and $l \le 2c + c^2/b$. Let
--
--   $$p^* = \frac{k(b+c)(l+m) + a[m(l+m) + (b+c)(l+2m)]}{c(b+c)(l+2m) + m(b+2c)(l+m)}, \qquad \alpha^* = \frac{(b+c+l+m)(am-ck)}{k(b+c)(l+m) + a[m(l+m)+(b+c)(l+2m)]}.$$
--
--   Then:
--   1. the symmetric profile in which both platforms play $(p^*, \alpha^*)$ is a Nash equilibrium, with positive demand and supply on both platforms;
--   2. $0 < \alpha^* < 1$;
--   3. it is the only symmetric Nash equilibrium with positive demand and supply: if both platforms play the same action $(p, \alpha)$, this is a Nash equilibrium, and demand and supply are positive, then $(p, \alpha) = (p^*, \alpha^*)$.
--
--   This is the DCR benchmark against which the two precommitment schemes are compared.
--
--   **Formalization Note** Uniqueness is among symmetric equilibria with positive demand and supply (p. 9: "the demand and supply should be positive"). With the truncated volume, zero-volume symmetric profiles (price above $a/c$) can be equilibria, and they are excluded.
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, p. 10 (PDF 11), Lemma 1, Equations (4)–(5); proof A.3, pp. 38–39 (PDF 39–40)

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

theorem lemma_1 (P : Params) (hP : P.Standing) :
    IsNashDCR P (pD P, alphaD P) (pD P, alphaD P) ∧
    NontrivialDCR P (pD P, alphaD P) (pD P, alphaD P) ∧
    0 < alphaD P ∧ alphaD P < 1 ∧
    ∀ x : ℝ × ℝ, IsNashDCR P x x → NontrivialDCR P x x → x = (pD P, alphaD P) := by sorry
end SharingPlatform.WageSchemes
