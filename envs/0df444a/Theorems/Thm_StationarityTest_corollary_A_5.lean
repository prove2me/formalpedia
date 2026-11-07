-- Prove2me | Theorems.Thm_StationarityTest_corollary_A_5
-- name    : StationarityTest.corollary_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:34.490399+00:00
-- url     : https://prove2.me/theorems/90d73a53-ab8e-40ba-9256-0711a8f567ad
-- title:
--   Corollary A.5 — if $H,G$ agree outside $B[i,\ell]$ then $\|\mathcal L^\dagger_{H,a}-\mathcal L^\dagger_{G,a}\|_{\infty-\infty}\le32\beta d\,\eta\,|B[i,\ell]|$
-- statement:
--   In the setting of Lemma A.4 (a common clause set $\Gamma$ of degree at most $d$, $|h_\gamma|,|g_\gamma|\le1$, $\beta>0$, a single-site Pauli jump $A^a$ on site $i$), let $\ell\ge1$ and $\eta\in[0,2]$. Suppose that
--
--   1. $|h_\gamma-g_\gamma|\le\eta$ for all $\gamma\in\Gamma$;
--   2. $h_\gamma=g_\gamma$ for all $\gamma\in\Gamma\setminus B[i,\ell]$.
--
--   Then
--
--   $$\big\|\mathcal L^\dagger_{H,a}-\mathcal L^\dagger_{G,a}\big\|_{\infty-\infty}\le32\beta d\cdot\eta\cdot|B[i,\ell]|.$$
--
--   A perturbation confined to a ball moves the local generator by an amount proportional to its size and to the volume of the ball. Lemma 5.4 uses this to compare the ideal grid point with the truth.
--
--   Differences from the source: none.
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Corollary A.5, (258), p.59

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Lindbladian

namespace StationarityTest

/-- **Corollary A.5 (H, G agree outside a neighborhood)**, p.59 (Bergamaschi, *The stationarity
test*, arXiv:2610.01074, held file sha256 0b7e46fb…). In the context of Lemma A.4, let `ℓ ≥ 1`,
`η ∈ [0, 2]`, `max_{γ∈Γ} |h_γ − g_γ| ≤ η` and `h_γ = g_γ` for all `γ ∉ B[i, ℓ]`. Then
`∥L†_{H,a} − L†_{G,a}∥_{∞−∞} ≤ 32βd · η · |B[i, ℓ]|` (258).

**Formalization Note.** `B[i, ℓ]` is the clause ball of site `i` in `Γ`; "`γ ∉ B[i, ℓ]`" ranges
over the clauses of `Γ`. -/
theorem corollary_A_5 {n q k d : ℕ} (Γ : Finset (KLocal n q k)) (hdeg : DegreeLe Γ d)
    (h g : KLocal n q k → ℝ) (hh : ∀ γ ∈ Γ, |h γ| ≤ 1) (hg : ∀ γ ∈ Γ, |g γ| ≤ 1)
    {β : ℝ} (hβ : 0 < β) (i : Fin n) (a : PauliString n q) (ha : a ∈ singleSite i)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {η : ℝ} (hη0 : 0 ≤ η) (hη2 : η ≤ 2)
    (hclose : ∀ γ ∈ Γ, |h γ - g γ| ≤ η)
    (hout : ∀ γ ∈ Γ, γ ∉ clauseBall Γ (Sum.inl i) ℓ → h γ = g γ) :
    superNorm (fun O => adjointSO (lindblad (ham Γ h) β a.mat) O -
        adjointSO (lindblad (ham Γ g) β a.mat) O) ≤
      32 * β * d * η * ((clauseBall Γ (Sum.inl i) ℓ).card : ℝ) := by sorry

end StationarityTest
