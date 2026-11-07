-- Prove2me | Theorems.Thm_StationarityTest_lemma_3_4
-- name    : StationarityTest.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:37.927277+00:00
-- url     : https://prove2.me/theorems/e9a1a1dd-4376-4ade-aa3e-ce99ebb6925a
-- title:
--   Lemma 3.4 — $\|[A^a,X]\|_\sigma^2\le c_1(e^\Omega\mathcal Q_a(X,G;\sigma)+c_{gr}^2\eta^2e^{-c_2\Omega})$ and the log-likelihood version
-- statement:
--   Fix $q,k,d,D\ge1$ and $c_{gr}\ge1$. There are $K\in\mathbb N$ and $c>0$ such that, with
--
--   $$c_1=\exp\big(K(\beta d)^K\big),\qquad c_2=\frac c{\beta d},$$
--
--   the following holds. Let $\beta d\ge1$ and let $G=\sum_{\gamma\in\Gamma}g_\gamma P_\gamma$ be a $(d,D,c_{gr})$ Hamiltonian with $|g_\gamma|\le1$. Let $\sigma$ be a full-rank state, $A^a$ a single-site Pauli operator, $\Omega>0$, and $X=\sum_{\gamma\in\Gamma}x_\gamma P_\gamma$ with $|x_\gamma|\le\eta$. Then:
--
--   1. $\displaystyle\|[A^a,X]\|_\sigma^2\le c_1\big(e^\Omega\,\mathcal Q_a(X,G;\sigma)+c_{gr}^2\eta^2e^{-c_2\Omega}\big);$
--   2. $\displaystyle\|[A^a,\beta G+\log\sigma]\|_\sigma^2\le c_1\big(e^\Omega\,\mathrm{FI}_{G,a}(\sigma\|\rho_G)+e^{-c_2\Omega}\|\beta G+\log\sigma\|^2\big).$
--
--   Here $\|\cdot\|_\sigma$ is the KMS norm and $\|\cdot\|$ the operator norm. Small Fisher information forces small commutators of the log-likelihood with every local jump, up to a high-frequency error that decays in $\Omega$.
--
--   Differences from the source:
--   - encoding: "c_1 ≤ e^{poly(βd,D)}, c_2 ∝ (βd)^{−1}" → ∃ K ∈ ℕ, c > 0 after q, k, d, D, c_gr with c_1 = exp(K(βd)^K), c_2 = c/(βd); reason: a larger c_1 or a smaller c_2 only weakens the bound, so fixing them at the extreme admitted value is the same claim; D is fixed, so poly(βd, D) is a polynomial in βd
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma 3.4, (56)–(57), p.20

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Fisher

namespace StationarityTest

/-- **Lemma 3.4 (The Fisher Information and gradients of the log-likelihood)**, p.20
(Bergamaschi, *The stationarity test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Fix
`β ≥ d^{−1}`. Let `G = Σ_{γ∈Γ} g_γ P_γ` be a `(d, D, c_gr)` Hamiltonian, `σ` a full-rank state and
`A_a` a single-site Pauli operator. Then for any `Ω > 0` and `X := Σ_{γ∈Γ} x_γ P_γ` with
`|x_γ| ≤ η`:

1. `∥[A_a, X]∥²_σ ≤ c₁(e^Ω Q_a(X, G; σ) + c_gr² η² e^{−c₂Ω})` (56);
2. `∥[A_a, βG + log σ]∥²_σ ≤ c₁(e^Ω FI_{G,a}(σ ∥ ρ_G) + e^{−c₂Ω} ∥βG + log σ∥²)` (57),

with constants `c₁ ≤ e^{poly(βd, D)}`, `c₂ ∝ (βd)^{−1}`.

**Formalization Note.** The constants: for fixed `q, k, d, D, c_gr` there are `K ∈ ℕ` and
`c > 0` with `c₁ = exp(K (βd)^K)` and `c₂ = c/(βd)`, uniformly in `n`, `β` (with `βd ≥ 1`),
`G`, `σ`, `a`, `Ω`, `η`, `X`. `∥·∥_σ` is the KMS norm (27); `∥·∥` in (57) is the operator norm.
`|g_γ| ≤ 1` is (21); `q, k, d, D ≥ 1`, `c_gr ≥ 1` are the paper's parameter ranges. -/
theorem lemma_3_4 : ∀ q k d D : ℕ, 1 ≤ q → 1 ≤ k → 1 ≤ d → 1 ≤ D → ∀ cgr : ℝ, 1 ≤ cgr →
    ∃ K : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ {n : ℕ} (Γ : Finset (KLocal n q k)), IsDDcgr d D cgr Γ →
    ∀ (g : KLocal n q k → ℝ), (∀ γ ∈ Γ, |g γ| ≤ 1) →
    ∀ {β : ℝ}, 1 ≤ β * d → ∀ (σ : Op n q), IsFullRankState σ →
    ∀ (i : Fin n) (a : PauliString n q), a ∈ singleSite i →
    ∀ {Ω : ℝ}, 0 < Ω → ∀ (η : ℝ) (x : KLocal n q k → ℝ), (∀ γ ∈ Γ, |x γ| ≤ η) →
    wNormSq σ 0 (comm a.mat (ham Γ x)) ≤
        Real.exp (K * (β * d) ^ K) *
          (Real.exp Ω * funcQ (ham Γ g) β a.mat (ham Γ x) σ +
            cgr ^ 2 * η ^ 2 * Real.exp (-(c / (β * d) * Ω))) ∧
      wNormSq σ 0 (comm a.mat (((β : ℝ) : ℂ) • ham Γ g + logM σ)) ≤
        Real.exp (K * (β * d) ^ K) *
          (Real.exp Ω * fisherInfo (ham Γ g) β a.mat σ +
            Real.exp (-(c / (β * d) * Ω)) *
              QAlgorithms.specNorm (((β : ℝ) : ℂ) • ham Γ g + logM σ) ^ 2) := by sorry

end StationarityTest
