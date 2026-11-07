-- Prove2me | Theorems.Thm_StationarityTest_lemma_A_7
-- name    : StationarityTest.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:31.990175+00:00
-- url     : https://prove2.me/theorems/af61b254-13cc-4988-8ce6-ff723a73bef4
-- title:
--   Lemma A.7 — shell decomposition: the radius-$b$ shell of a local perturbation $U$ moves $\mathcal L^\dagger_{\cdot,a}$ by at most $\mathrm{poly}(\beta d)\|U\|e^{-c_1(b-\ell)}$
-- statement:
--   Fix $q,k,d\ge1$. There are $K\in\mathbb N$ and $c>0$ such that the following holds. Let $\Gamma$ be a clause set of degree at most $d$, and let $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ and $G=H+U=\sum_{\gamma\in\Gamma}g_\gamma P_\gamma$ with $|h_\gamma|,|g_\gamma|\le1$. Let $\beta d\ge1$, $A^a$ a single-site Pauli on site $i$, $\ell\ge1$, and suppose $h_\gamma=g_\gamma$ for every $\gamma\in\Gamma\setminus B[i,\ell]$. For $b\ge\ell$ write $H_b=H_{B[i,b]}$ and $G_b=G_{B[i,b]}$ for the truncations to the clause ball of radius $b$. Then
--
--   $$\Big\|\big(\mathcal L^\dagger_{G_{b+1},a}-\mathcal L^\dagger_{H_{b+1},a}\big)-\big(\mathcal L^\dagger_{G_b,a}-\mathcal L^\dagger_{H_b,a}\big)\Big\|_{\infty-\infty}\le K(\beta d)^K\,\|U\|\,e^{-\frac c{\beta d}(b-\ell)}.$$
--
--   The effect of a local perturbation $U$ on the generator is carried by shells around $i$ whose contributions decay exponentially with the radius. Lemma 5.6 uses this to truncate the perturbative correction to a constant radius.
--
--   Differences from the source:
--   - encoding: "poly(β·d)", "c_1 ∝ (βd)^{−1}" → K(βd)^K and c_1 = c/(βd), with K ∈ ℕ, c > 0 chosen after q, k, d; reason: the meaning of poly and ∝ with the Hamiltonian parameters fixed
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma A.7, (262), p.60

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Lindbladian

namespace StationarityTest

/-- **Lemma A.7 (A shell decomposition for Corollary A.6)**, p.60 (Bergamaschi, *The
stationarity test*, arXiv:2610.01074, held file sha256 0b7e46fb…). In the context of Lemma A.4,
let `βd ≥ 1`, `ℓ ≥ 1`, and let `H`, `G = H + U` be degree-`d` Hamiltonians on the same
interaction graph with `h_γ = g_γ` for all `γ ∉ B[i, ℓ]`. For `b ≥ ℓ` let `H_b := H_{B[i,b]}`,
`G_b := G_{B[i,b]}` be the truncations to radius `b`. Then
`∥(L†_{G_{b+1},a} − L†_{H_{b+1},a}) − (L†_{G_b,a} − L†_{H_b,a})∥_{∞−∞} ≤ poly(βd) ∥U∥ e^{−c₁(b−ℓ)}`
(262), where `c₁ ∝ (βd)^{−1}`.

**Formalization Note.** `poly(βd) = K (βd)^K` and `c₁ = c/(βd)`, with `K`, `c > 0` depending only
on `q, k, d`. `∥U∥` is the operator norm of `G − H`. Truncation `H_{B[i,b]}` keeps the clauses of
the clause ball of `i` of radius `b` in `Γ`. `|h_γ|, |g_γ| ≤ 1` is (21). -/
theorem lemma_A_7 : ∀ q k d : ℕ, 1 ≤ q → 1 ≤ k → 1 ≤ d → ∃ K : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ {n : ℕ} (Γ : Finset (KLocal n q k)), DegreeLe Γ d →
    ∀ (h g : KLocal n q k → ℝ), (∀ γ ∈ Γ, |h γ| ≤ 1) → (∀ γ ∈ Γ, |g γ| ≤ 1) →
    ∀ {β : ℝ}, 1 ≤ β * d → ∀ (i : Fin n) (a : PauliString n q), a ∈ singleSite i →
    ∀ (ℓ : ℕ), 1 ≤ ℓ → (∀ γ ∈ Γ, γ ∉ clauseBall Γ (Sum.inl i) ℓ → h γ = g γ) →
    ∀ (b : ℕ), ℓ ≤ b →
    superNorm (fun O =>
        (adjointSO (lindblad (ham (clauseBall Γ (Sum.inl i) (b + 1)) g) β a.mat) O -
          adjointSO (lindblad (ham (clauseBall Γ (Sum.inl i) (b + 1)) h) β a.mat) O) -
        (adjointSO (lindblad (ham (clauseBall Γ (Sum.inl i) b) g) β a.mat) O -
          adjointSO (lindblad (ham (clauseBall Γ (Sum.inl i) b) h) β a.mat) O)) ≤
      K * (β * d) ^ K * QAlgorithms.specNorm (ham Γ g - ham Γ h) *
        Real.exp (-(c / (β * d) * ((b : ℝ) - ℓ))) := by sorry

end StationarityTest
