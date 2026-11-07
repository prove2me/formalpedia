-- Prove2me | Theorems.Thm_StationarityTest_lemma_5_6
-- name    : StationarityTest.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:54.923362+00:00
-- url     : https://prove2.me/theorems/f8ba77f1-c7d6-4e6d-ab2c-11619ceb9416
-- title:
--   Lemma 5.6 — $\mathrm{Test}_i[P,G^{(r)}+\eta_rU;\rho_H]$ is a log-radius baseline plus a constant-radius correction
-- statement:
--   Fix $q,k,d,D\ge1$ and $c_{gr}\ge1$. There are $K\in\mathbb N$ and $c>0$ such that, with $c_1=c/(\beta d)$, the following holds. Let $n\ge1$, $\beta d\ge1$ and let $H$ be a $(d,D,c_{gr})$ Hamiltonian with $|h_P|\le1$. Let $r\ge0$, $\eta_r=2^{-r}$, and let $G^{(r)}$ satisfy $\max_P|g_P-h_P|\le\eta_r$ and $\Gamma_{G^{(r)}}\subseteq\Gamma_H$. Let $\ell>1$, $\kappa\in(0,1)$, and let $(i,\Lambda,U)$ be considered by Algorithm 3. Write $\hat\Gamma=\Gamma_{G^{(r)}}\cup\Lambda$ and $\hat G_L=G^{(r)}_{B_{\hat\Gamma}[i,L]}$. Then for all radii $R$ and $L\ge\ell$ and every $P\in S^k_{[n]}$,
--
--   $$\Big|\mathrm{Test}_i[P,G^{(r)}+\eta_rU;\rho_H]-\mathrm{Test}_i[P,G^{(r)}_{B[i,R]};\rho_H]-\operatorname{tr}\big[(\mathcal L^\dagger_{\hat G_L+\eta_rU,i}-\mathcal L^\dagger_{\hat G_L,i})[P]\rho_H\big]\Big|$$
--   $$\le K(\beta d)^K\ell^K\big(e^{-c_1R}+\eta_r\,e^{-c_1(L-\ell)}\big).$$
--
--   The ball $B[i,R]$ is taken in the interaction graph of $G^{(r)}$. The baseline term depends only on $G^{(r)}$, and the correction lives on a constant-radius patch. This is what allows all perturbed tests to be measured in parallel from $O(\log n)$ samples.
--
--   Differences from the source:
--   - reading: "considered by Algorithm 3" after the rth iteration → Considered (Λ ∈ CC_{i,ℓ}, Γ_{G^(r)} ∪ Λ is (d, D, c_gr), U ∈ Grid(Λ)), η_r = 2^{−r}, max_P |g_P − h_P| ≤ η_r and Γ_{G^(r)} ⊆ Γ_H; reason: the context of Algorithm 3 and the invariant (107) of Lemma 5.4, which the proof uses through Corollary A.6
--   - encoding: "poly(β·d, ℓ)", "c_1 ∝ (β·d)^{−1}" → K(βd)^Kℓ^K and c/(βd), with K, c chosen after q, k, d, D, c_gr and before ℓ, κ, the radii and the instance; reason: the meaning of poly and ∝ with the Hamiltonian parameters fixed
--   - reading: "G^(r)_{B[i,R(r)]}" → the truncation of G^(r) to the clause ball of i in Γ_{G^(r)}; reason: proof of Lemma 5.6, (126): "radius R(r), defined by the distance on the interaction graph of G(r)"
--   - generalization: the parameters ℓ, κ of Algorithm 3 ("fixed constants ℓ > 1, κ, c_meas > 0", p.28, chosen in Lemma 5.4) and the radius R^(r) = ℓ + O(log η_r^{−1}) (p.33) → every ℓ > 1, every κ > 0 and every radius R ∈ ℕ; reason: the bound (125) is stated in terms of R^(r) and ℓ, and the paper's choices are instances
--   - reading: "patches of some constant radius L ≫ ℓ" (p.33) → every radius L ∈ ℕ with L ≥ ℓ; reason: the outline's L ≫ ℓ, and Lemma A.7 (b ≥ ℓ), through which the proof truncates to radius L
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma 5.6, (124)–(125), p.33 (proof (126)–(128), pp.33–34)

import Definitions.Def_StationarityTest_Algorithm

open Matrix

namespace StationarityTest

/-- **Lemma 5.6**, p.33 (Bergamaschi, *The stationarity test*, arXiv:2610.01074, held file sha256
0b7e46fb…). Fix `βd ≥ 1` and a triple `i ∈ [n]`, `Λ ∈ CC_{i,ℓ}`, `U ∈ Grid(Λ)` considered by
Algorithm 3. Let `Ĝ_L := G^(r)_{B_Γ̂[i,L]}` be the truncation of `G^(r)` to the clauses at radius
`≤ L` in `Γ̂ := Γ_{G^(r)} ∪ Λ`. Then
`Test_i[P, G^(r) + η_r U; ρ_H] ≈ Test_i[P, G^(r)_{B[i,R(r)]}; ρ_H] + tr[(L†_{Ĝ_L+η_r U,i} − L†_{Ĝ_L,i})[P] ρ_H]`
(124) to error `≤ poly(βd, ℓ)(e^{−c₁R(r)} + η_r e^{−c₁(L−ℓ)})` (125), where `c₁ ∝ (βd)^{−1}`.

**Formalization Note.** `poly(βd, ℓ) = K (βd)^K ℓ^K` and `c₁ = c/(βd)`, with `K`, `c > 0`
depending only on `q, k, d, D, c_gr`; the statement holds for every `ℓ > 1`, `κ > 0` (p.28), every
radius `R(r)` and every `L ≥ ℓ`, and every `P ∈ S^k_[n]`. "Considered by Algorithm 3" is
`Considered` (Definition 5.2, (102), line 2), in the round-`r` context of Lemma 5.5:
`η_r = 2^{−r}`, `G^(r)` accurate to `η_r` and `Γ_{G^(r)} ⊆ Γ_H` (the invariant (107)), `H` a
`(d, D, c_gr)` Hamiltonian with `|h_P| ≤ 1`. `G^(r)_{B[i,R]}` is the truncation in the
interaction graph of `G^(r)` (proof of Lemma 5.6, (126)). -/
theorem lemma_5_6 : ∀ q k d D : ℕ, 1 ≤ q → 1 ≤ k → 1 ≤ d → 1 ≤ D → ∀ cgr : ℝ, 1 ≤ cgr →
    ∃ K : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, 1 ≤ n → ∀ β : ℝ, 1 ≤ β * d → ∀ h : KLocal n q k → ℝ, (∀ P, |h P| ≤ 1) →
    IsDDcgr d D cgr (coeffSupport h) →
    ∀ (r : ℕ) (g : KLocal n q k → ℝ), (∀ P, |g P - h P| ≤ ((2 : ℝ) ^ r)⁻¹) →
    (∀ P, g P ≠ 0 → h P ≠ 0) →
    ∀ (ℓ : ℕ), 1 < ℓ → ∀ (κ : ℝ), 0 < κ →
    ∀ (i : Fin n) (Λ : Finset (KLocal n q k)) (U : KLocal n q k → ℝ),
    Considered ℓ d D cgr κ g i Λ U →
    ∀ (L R : ℕ), ℓ ≤ L → ∀ P : KLocal n q k,
    ‖testSite i β P.1.mat (ham Finset.univ fun Q => g Q + ((2 : ℝ) ^ r)⁻¹ * U Q)
          (gibbs β (ham Finset.univ h)) -
        (testSite i β P.1.mat (ham (clauseBall (coeffSupport g) (Sum.inl i) R) g)
            (gibbs β (ham Finset.univ h)) +
          trace (gibbs β (ham Finset.univ h) *
            (adjointSO (lindbladSite (ham (clauseBall (coeffSupport g ∪ Λ) (Sum.inl i) L) g +
                ((((2 : ℝ) ^ r)⁻¹ : ℝ) : ℂ) • ham Finset.univ U) β i) P.1.mat -
              adjointSO (lindbladSite (ham (clauseBall (coeffSupport g ∪ Λ) (Sum.inl i) L) g)
                β i) P.1.mat)))‖ ≤
      K * (β * d) ^ K * (ℓ : ℝ) ^ K *
        (Real.exp (-(c / (β * d) * R)) +
          ((2 : ℝ) ^ r)⁻¹ * Real.exp (-(c / (β * d) * ((L : ℝ) - ℓ)))) := by sorry

end StationarityTest
