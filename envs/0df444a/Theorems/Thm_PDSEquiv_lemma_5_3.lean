-- Prove2me | Theorems.Thm_PDSEquiv_lemma_5_3
-- name    : PDSEquiv.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:33.273039+00:00
-- url     : https://prove2.me/theorems/6d4f6a4e-ae63-4896-a7cc-87ffd750db51
-- title:
--   Lemma 5.3 — high vertex-degree part: advantage $(1+\xi)\Lambda_N(k)$ forces $|\mathbb E_{\mathrm{PDS}}f^{>D}|\ge(\xi/2)\Lambda_N(k)\ge N^{-2}$
-- statement:
--   Fix $0<q<p\le1$, an integer $D\ge2$ and constants $u<1/2$, $\xi>0$. For every sufficiently large $N$ and every integer $2\le k\le N^u$: if $f:\mathcal G_N\to[-1,1]$ satisfies $\mathrm{adv}_f(\mathrm{PDS}(N,k,p,q),\mathrm{ER}(N,q))\ge(1+\xi)\Lambda_N(k)$, then
--   $$\Bigl|\mathbb E_{G\sim\mathrm{PDS}}\bigl[f^{>D}(G)\bigr]\Bigr|\ \ge\ \frac\xi2\Lambda_N(k)\ \ge\ N^{-2}.$$
--
--   Any advantage beyond the edge-count benchmark therefore shows up in the high vertex-degree part of $f$, which is what the embedding can amplify.
--
--   Differences from the source:
--   - encoding: for every sufficiently large N and every integer 2 ≤ k ≤ N^u → ∃ N₀ chosen before k and f, ∀ N ≥ N₀; reason: the quantifier order of the page
--   - encoding: standing densities of §5 → real binders 0 < q < p ≤ 1; reason: the section's standing assumption
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Lemma 5.3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Fourier

set_option autoImplicit false

namespace PDSEquiv

/-- S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Lemma 5.3, p.14 (PDF p.16).
For every sufficiently large `N` and every integer `2 ≤ k ≤ N^u`: if `f : G_N → [−1, 1]` has
`adv_f(PDS, ER) ≥ (1 + ξ) Λ_N(k)`, then `|E_{PDS}[f^{>D}]| ≥ (ξ/2) Λ_N(k) ≥ N^{−2}`. -/
theorem lemma_5_3 (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p ≤ 1) (D : ℕ) (hD : 2 ≤ D) (u ξ : ℝ)
    (hu : u < 1 / 2) (hξ : 0 < ξ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ, 2 ≤ k → (k : ℝ) ≤ (N : ℝ) ^ u →
      ∀ f : Graph N → ℝ, (∀ G, |f G| ≤ 1) →
        advF (pdsMass N k p q) (erMass N q) f ≥ (1 + ξ) * Lam p q N k →
        |expect (pdsMass N k p q) (highPart q D f)| ≥ ξ / 2 * Lam p q N k ∧
          ξ / 2 * Lam p q N k ≥ (N : ℝ) ^ (-(2 : ℝ)) := by sorry

end PDSEquiv
