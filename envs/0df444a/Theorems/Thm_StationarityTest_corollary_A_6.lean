-- Prove2me | Theorems.Thm_StationarityTest_corollary_A_6
-- name    : StationarityTest.corollary_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:29.040099+00:00
-- url     : https://prove2.me/theorems/4bdc826d-69f7-4ae9-9533-230f39db3862
-- title:
--   Corollary A.6 — if $H,G$ agree on $B[i,\ell]$ then $\|\mathcal L^\dagger_{H,a}-\mathcal L^\dagger_{G,a}\|_{\infty-\infty}\le c_{gr}c_D(\beta d)^{D+1}\eta\,e^{-\ell\theta/2}$
-- statement:
--   For every $D\ge1$ there is a constant $c_D$, depending only on $D$, with the following property. Let $d\ge1$, $c_{gr}\ge1$, let $\Gamma\subseteq S^k_{[n]}$ be the clause set of a $(d,D,c_{gr})$ Hamiltonian, and let $H,G$ have coefficients on $\Gamma$ with $|h_\gamma|,|g_\gamma|\le1$. Let $\beta>d^{-1}$, $A^a$ a single-site Pauli on site $i$, $\ell\ge1$ and $\eta\in[0,2]$. Suppose that
--
--   1. $|h_\gamma-g_\gamma|\le\eta$ for all $\gamma\in\Gamma$;
--   2. $h_\gamma=g_\gamma$ for all $\gamma\in B[i,\ell]$.
--
--   Then, with $\theta=\min\{1,(8e\beta d)^{-1}\}$,
--
--   $$\big\|\mathcal L^\dagger_{H,a}-\mathcal L^\dagger_{G,a}\big\|_{\infty-\infty}\le c_{gr}\,c_D\,(\beta d)^{D+1}\,\eta\,e^{-\ell\theta/2}.$$
--
--   Distant perturbations barely affect the local generator. This quasi-locality is what allows stationarity tests to be truncated to logarithmic radius.
--
--   Differences from the source:
--   - encoding: "c_D is a function only of D" → ∀ D ≥ 1, ∃ c_D, then every other parameter; reason: the meaning of the dependence clause
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Corollary A.6, (259), p.59 (proof (260)–(261))

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Lindbladian

namespace StationarityTest

/-- **Corollary A.6 (H, G agree within a neighborhood)**, p.59 (Bergamaschi, *The stationarity
test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Fix `β > d^{−1}`. In the context of
Lemma A.4, let `ℓ ≥ 1`, `η ∈ [0, 2]`, `max_{γ∈Γ} |h_γ − g_γ| ≤ η` and `h_γ = g_γ` for all
`γ ∈ B[i, ℓ]`, and let `H, G` be `(d, D, c_gr)` Hamiltonians. Then
`∥L†_{H,a} − L†_{G,a}∥_{∞−∞} ≤ c_gr · c_D · (βd)^{D+1} · η · e^{−ℓθ/2}` (259), where `c_D`
depends only on `D` and `θ = min{1, (8eβd)^{−1}}`.

**Formalization Note.** "`c_D` is a function only of `D`": `∃ c_D` after `D` and before
everything else. Both Hamiltonians live on the common clause set `Γ`, which is `(d, D, c_gr)`
(Definition 2.2, with its ranges `d, D ≥ 1`, `c_gr ≥ 1`). `β > d^{−1}` is strict, as printed. -/
theorem corollary_A_6 : ∀ D : ℕ, 1 ≤ D → ∃ cD : ℝ, ∀ {n q k d : ℕ} {cgr : ℝ}, 1 ≤ d → 1 ≤ cgr →
    ∀ (Γ : Finset (KLocal n q k)), IsDDcgr d D cgr Γ →
    ∀ (h g : KLocal n q k → ℝ), (∀ γ ∈ Γ, |h γ| ≤ 1) → (∀ γ ∈ Γ, |g γ| ≤ 1) →
    ∀ {β : ℝ}, 1 < β * d → ∀ (i : Fin n) (a : PauliString n q), a ∈ singleSite i →
    ∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ {η : ℝ}, 0 ≤ η → η ≤ 2 → (∀ γ ∈ Γ, |h γ - g γ| ≤ η) →
    (∀ γ ∈ clauseBall Γ (Sum.inl i) ℓ, h γ = g γ) →
    superNorm (fun O => adjointSO (lindblad (ham Γ h) β a.mat) O -
        adjointSO (lindblad (ham Γ g) β a.mat) O) ≤
      cgr * cD * (β * d) ^ (D + 1) * η *
        Real.exp (-(ℓ * min 1 (8 * Real.exp 1 * β * d)⁻¹ / 2)) := by sorry

end StationarityTest
