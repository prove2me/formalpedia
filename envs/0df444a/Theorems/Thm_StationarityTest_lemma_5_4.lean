-- Prove2me | Theorems.Thm_StationarityTest_lemma_5_4
-- name    : StationarityTest.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:13.154382+00:00
-- url     : https://prove2.me/theorems/e80df18d-0202-4f00-8673-1a16f6006ab7
-- title:
--   Lemma 5.4 — one round of Algorithm 3 keeps $\Gamma_{G^{(r)}}\subseteq\Gamma_{G^{(r+1)}}\subseteq\Gamma_H$ and halves the error
-- statement:
--   Fix $q,k,d,D\ge1$, $c_{gr}\ge1$ and $\beta$ with $\beta d\ge1$. There are algorithm parameters $\ell>1$, $\kappa\in(0,1)$ and $c_{\mathrm{meas}}\in(0,1]$ such that the following holds. Let $n\ge1$ and let $H=\sum_Ph_PP$ be an $n$-qudit $(d,D,c_{gr})$ Hamiltonian with $|h_P|\le1$. Let $r\ge0$, $\eta_r=2^{-r}$, and let the guess $G^{(r)}=\sum_Pg_PP$ satisfy
--
--   $$\max_{P\in S^k_{[n]}}|g_P-h_P|\le\eta_r,\qquad|h_P|\ge\tfrac7{16}\eta_r\ \text{ for all }P\in\Gamma_{G^{(r)}}.$$
--
--   Let $G^{(r+1)}=\sum_Pg'_PP$ be an output of one round of Algorithm 3 in which every estimate is within $c_{\mathrm{meas}}\eta_r$. Then $\Gamma_{G^{(r)}}\subseteq\Gamma_{G^{(r+1)}}\subseteq\Gamma_H$ and
--
--   $$\max_{P\in S^k_{[n]}}|g'_P-h_P|\le\eta_{r+1},\qquad|h_P|\ge\tfrac7{16}\eta_{r+1}\ \text{ for all }P\in\Gamma_{G^{(r+1)}}.$$
--
--   The invariant is preserved and the error halves. Starting from $G^{(0)}=0$, $\eta_0=1$, after $\lceil\log_21/\eta\rceil$ rounds the guess has the right support and accuracy $\eta$.
--
--   **Formalization Note** A round is any output of the relation `IsRound3`: any estimates within tolerance, any minimizer, any order of the site updates.
--
--   Differences from the source:
--   - generalization: "the output Hamiltonian G^(r+1)" of Algorithm 3 (one processing order of the sites, one choice of minimizer) → every output of the round relation: every minimizer, and every assignment P ↦ i(P) ∈ supp(P) of the site whose update (103) is final; reason: the paper's run is one instance; the proof's case analysis (118)–(120) applies to every site
--   - generalization: "There exists choices of (ℓ, κ, c_meas)" → ∃ ℓ > 1, κ ∈ (0, 1), c_meas ∈ (0, 1]; reason: the ranges p.28 and Lemma 4.3 fix for these parameters; the proof's choices κ = c_meas = e^{−c₁ℓ} lie in them, and dropping the ranges gives the source's claim
--   - encoding: η_r, the rth accuracy → η_r = 2^{−r}; reason: p.28: "accuracy η_r := 2^{−r}"
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma 5.4, (107)–(108), p.30 (proof (109)–(120), pp.30–32)

import Definitions.Def_StationarityTest_Algorithm

namespace StationarityTest

/-- **Lemma 5.4 (Correctness of a single iteration)**, p.30 (Bergamaschi, *The stationarity
test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Fix `βd ≥ 1`. There exist choices of
`(ℓ, κ, c_meas)` as a function of `β` and the Hamiltonian parameters such that: if in the `r`-th
iteration the guess `G^(r) = Σ_P g^(r)_P P` satisfies
`max_{P∈S^k_[n]} |g^(r)_P − h_P| ≤ η_r` and `|h_P| ≥ (7/16) η_r` for all `P ∈ Γ_{G^(r)}` (107),
and every estimate in Algorithm 3 is within `c_meas · η_r`, then the output `G^(r+1)` satisfies
`Γ_{G^(r)} ⊆ Γ_{G^(r+1)} ⊆ Γ_H`, `max_P |g^(r+1)_P − h_P| ≤ η_{r+1}` and
`|h_P| ≥ (7/16) η_{r+1}` for all `P ∈ Γ_{G^(r+1)}` (108).

**Formalization Note.** `η_r = 2^{−r}`. `H` is an `n`-qudit `(d, D, c_gr)` Hamiltonian
(Definition 2.2 on `Γ_H`) with `|h_P| ≤ 1` (100). The parameters are chosen after
`q, k, d, D, c_gr, β` and before `n`, `H`, `r`, in the ranges `ℓ > 1`, `0 < κ < 1` (p.28, (74))
and `0 < c_meas ≤ 1` (Lemma 4.3). The output is any `G^(r+1)` related to `G^(r)` by one round of
Algorithm 3 (`IsRound3`): every family of estimates within tolerance, every minimizer, and every
order of the site updates. `Γ_G ⊆ Γ_{G'}` is `g_P ≠ 0 → g'_P ≠ 0`. -/
theorem lemma_5_4 : ∀ q k d D : ℕ, 1 ≤ q → 1 ≤ k → 1 ≤ d → 1 ≤ D → ∀ cgr : ℝ, 1 ≤ cgr →
    ∀ β : ℝ, 1 ≤ β * d →
    ∃ ℓ : ℕ, 1 < ℓ ∧ ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ cmeas : ℝ, 0 < cmeas ∧ cmeas ≤ 1 ∧
    ∀ n : ℕ, 1 ≤ n → ∀ h : KLocal n q k → ℝ, (∀ P, |h P| ≤ 1) →
    IsDDcgr d D cgr (coeffSupport h) →
    ∀ (r : ℕ) (g : KLocal n q k → ℝ)
      (T : Fin n → Finset (KLocal n q k) → (KLocal n q k → ℝ) → ℝ)
      (choice : Fin n → Finset (KLocal n q k) × (KLocal n q k → ℝ))
      (site : KLocal n q k → Fin n) (g' : KLocal n q k → ℝ),
    (∀ P, |g P - h P| ≤ ((2 : ℝ) ^ r)⁻¹) →
    (∀ P, g P ≠ 0 → 7 / 16 * ((2 : ℝ) ^ r)⁻¹ ≤ |h P|) →
    IsRound3 β ℓ d D cgr κ cmeas ((2 : ℝ) ^ r)⁻¹ h g T choice site g' →
    (∀ P, g P ≠ 0 → g' P ≠ 0) ∧ (∀ P, g' P ≠ 0 → h P ≠ 0) ∧
      (∀ P, |g' P - h P| ≤ ((2 : ℝ) ^ (r + 1))⁻¹) ∧
      ∀ P, g' P ≠ 0 → 7 / 16 * ((2 : ℝ) ^ (r + 1))⁻¹ ≤ |h P| := by sorry

end StationarityTest
