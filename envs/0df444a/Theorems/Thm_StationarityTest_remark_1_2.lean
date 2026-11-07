-- Prove2me | Theorems.Thm_StationarityTest_remark_1_2
-- name    : StationarityTest.remark_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:55.312099+00:00
-- url     : https://prove2.me/theorems/17cb64e6-b974-47e8-9efa-97e15224bc60
-- title:
--   Remark 1.2 — completeness: $\mathrm{Test}_a[O,H;\rho_H]=0$ for every jump and $\mathrm{Test}_i[O,H;\rho_H]=0$
-- statement:
--   Let $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ be a Hamiltonian with real coefficients, $\beta>0$, $i$ a site and $O$ any operator. If the guess equals the truth, $G=H$, and the sample is $\sigma=\rho_H$, then
--
--   $$\mathrm{Test}_a[O,H;\rho_H]=0\quad\text{for every }a\in S_i,\qquad\text{hence}\qquad \mathrm{Test}_i[O,H;\rho_H]=0.$$
--
--   This is detailed balance of the [CKG23] Lindbladian: $\mathcal L_{H,a}[\rho_H]=0$. It is the completeness half of the stationarity test, and the base point that every perturbation estimate in Algorithm 3 compares against.
--
--   Differences from the source:
--   - generalization: "Test_i[O, H; ρ_H] = 0" for the site sum, H a k-local Hamiltonian with |h_γ| ≤ 1 → the vanishing for every single jump a ∈ S_i as well as for the sum; any real coefficients on any clause set; reason: the per-jump statement implies the sum, and detailed balance holds jump by jump with no bound on the coefficients; the source's case is an instance
--   - generalization: "every observable O" → every operator O (not necessarily Hermitian); reason: the test is linear in O; Hermitian O are an instance
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Remark 1.2, p.4

import Definitions.Def_StationarityTest_Lindbladian

namespace StationarityTest

/-- **Remark 1.2 (Completeness)**, p.4 (Bergamaschi, *The stationarity test*, arXiv:2610.01074,
held file sha256 0b7e46fb…). If the sample is the Gibbs state `σ := ρ_H` and the guess is `G = H`,
detailed balance gives `Test_i[O, H; ρ_H] = 0` for every observable `O` and every site `i`.

Stated for every single-site Pauli jump `a ∈ S_i` separately, which implies the site sum, and
for the site sum `Test_i = Test_{S_i}` itself.

**Formalization Note.** `H = Σ_{γ∈Γ} h_γ P_γ` with any real coefficients on any clause set; `O`
is any operator; the Lindbladian is Definition 2.17 with `σ = β^{−1}` and the principal-value
coherent term. -/
theorem remark_1_2 {n q k : ℕ} (Γ : Finset (KLocal n q k)) (h : KLocal n q k → ℝ) {β : ℝ}
    (hβ : 0 < β) (i : Fin n) (O : Op n q) :
    (∀ a ∈ singleSite i, testJump a β O (ham Γ h) (gibbs β (ham Γ h)) = 0) ∧
      testSite i β O (ham Γ h) (gibbs β (ham Γ h)) = 0 := by sorry

end StationarityTest
