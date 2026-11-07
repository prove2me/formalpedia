-- Prove2me | Theorems.Thm_StationarityTest_lemma_3_3
-- name    : StationarityTest.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:33.777862+00:00
-- url     : https://prove2.me/theorems/a8d3fa41-1312-4519-88ca-cefe3ba6dc66
-- title:
--   Lemma 3.3 — convexity: $\max_{\gamma\ni i}|g_\gamma-h_\gamma|\le c_1(e^\Omega\,\mathrm{FI}_{G,i}(\rho_H\|\rho_G)^{1/2}+c_{gr}e^{-c_2\Omega}\eta)$
-- statement:
--   Fix $q,k,d,D\ge1$ and $c_{gr}\ge1$. There are $K\in\mathbb N$ and $c>0$ such that, with $c_1=\exp(K(\beta d)^K)$ and $c_2=c/(\beta d)$, the following holds. Let $\beta d\ge1$, and let $G=\sum_{\gamma\in\Gamma}g_\gamma P_\gamma$ and $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ be $(d,D,c_{gr})$ Hamiltonians on a common clause set with $|g_\gamma|,|h_\gamma|\le1$ and $\max_{\gamma\in\Gamma}|h_\gamma-g_\gamma|\le\eta$. Then for every site $i$, every $\Omega>0$ and every clause $\gamma\in\Gamma$ containing $i$,
--
--   $$|g_\gamma-h_\gamma|\le c_1\Big(e^\Omega\,\mathrm{FI}_{G,i}(\rho_H\|\rho_G)^{1/2}+c_{gr}\,e^{-c_2\Omega}\,\eta\Big).$$
--
--   This is the soundness of the stationarity test. If the Fisher information at site $i$ is small, every coefficient near $i$ is close to the truth, up to a fraction of the global error $\eta$ that the iteration can halve.
--
--   Differences from the source:
--   - encoding: "0 < c_1 ≤ e^{poly(βd,D)}, c_2 ∝ (β·d)^{−1}" → ∃ K ∈ ℕ, c > 0 after q, k, d, D, c_gr with c_1 = exp(K(βd)^K), c_2 = c/(βd); reason: as in Lemma 3.4: the bound is monotone in c_1 and c_2
--   - encoding: "max_{γ∋i} |g_γ − h_γ| ≤ …" → the bound for every γ ∈ Γ with i ∈ supp(γ); reason: a maximum over a possibly empty finite set; the bound for each element is the same claim
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma 3.3, (55), p.20 (proof (60)–(61), p.21)

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Fisher

namespace StationarityTest

/-- **Lemma 3.3 (Convexity of the Fisher Information)**, p.20 (Bergamaschi, *The stationarity
test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Fix `β ≥ d^{−1}`. Let
`G = Σ_{γ∈Γ} g_γ P_γ`, `H = Σ_{γ∈Γ} h_γ P_γ` be `(d, D, c_gr)` Hamiltonians with
`max_{γ∈Γ} |h_γ − g_γ| ≤ η`. Then for every site `i` and `Ω > 0`,
`max_{γ∋i} |g_γ − h_γ| ≤ c₁ (e^Ω FI_{G,i}(ρ_H ∥ ρ_G)^{1/2} + c_gr e^{−c₂Ω} η)` (55), with
`0 < c₁ ≤ e^{poly(βd, D)}` and `c₂ ∝ (βd)^{−1}`.

**Formalization Note.** Constants as in Lemma 3.4: `c₁ = exp(K (βd)^K)`, `c₂ = c/(βd)` with `K`,
`c > 0` depending only on `q, k, d, D, c_gr`. The maximum over `γ ∋ i` is a bound for every
clause `γ ∈ Γ` containing `i`. `FI_{G,i} = Σ_{a∈S_i} FI_{G,a}`; `(·)^{1/2}` is `Real.sqrt` (the
Fisher information is nonnegative). `|h_γ|, |g_γ| ≤ 1` is (21). -/
theorem lemma_3_3 : ∀ q k d D : ℕ, 1 ≤ q → 1 ≤ k → 1 ≤ d → 1 ≤ D → ∀ cgr : ℝ, 1 ≤ cgr →
    ∃ K : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ {n : ℕ} (Γ : Finset (KLocal n q k)), IsDDcgr d D cgr Γ →
    ∀ (g h : KLocal n q k → ℝ), (∀ γ ∈ Γ, |g γ| ≤ 1) → (∀ γ ∈ Γ, |h γ| ≤ 1) →
    ∀ (η : ℝ), (∀ γ ∈ Γ, |h γ - g γ| ≤ η) →
    ∀ {β : ℝ}, 1 ≤ β * d → ∀ (i : Fin n) {Ω : ℝ}, 0 < Ω →
    ∀ γ ∈ Γ, i ∈ siteSupport γ.1 →
    |g γ - h γ| ≤ Real.exp (K * (β * d) ^ K) *
      (Real.exp Ω * Real.sqrt (fisherSite (ham Γ g) β i (gibbs β (ham Γ h))) +
        cgr * Real.exp (-(c / (β * d) * Ω)) * η) := by sorry

end StationarityTest
