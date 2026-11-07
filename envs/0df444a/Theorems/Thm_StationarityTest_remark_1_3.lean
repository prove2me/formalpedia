-- Prove2me | Theorems.Thm_StationarityTest_remark_1_3
-- name    : StationarityTest.remark_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:43.05386+00:00
-- url     : https://prove2.me/theorems/0394c710-96a4-4372-881b-fcde342cc9dd
-- title:
--   Remark 1.3 (4) with Definition 2.21 (47) — $\mathrm{FI}_{G,a}(\rho_H\|\rho_G)=\beta\,\mathrm{Test}_a[H-G,G;\rho_H]$ and $\mathrm{FI}_{G,a}(\sigma\|\rho_G)=\mathcal Q_a(\log\sigma-\log\rho_G,G;\sigma)$
-- statement:
--   Let $H$ and $G$ be Hamiltonians with real coefficients on $S^k_{[n]}$ and $\beta>0$.
--
--   1. For every Pauli jump $a$ and every site $i$,
--   $$\mathrm{FI}_{G,a}(\rho_H\|\rho_G)=\beta\,\mathrm{Test}_a[H-G,G;\rho_H],\qquad \mathrm{FI}_{G,i}(\rho_H\|\rho_G)=\beta\,\mathrm{Test}_i[H-G,G;\rho_H].$$
--   2. For every Pauli jump $a$ and every full-rank state $\sigma$,
--   $$\mathrm{FI}_{G,a}(\sigma\|\rho_G)=\mathcal Q_a(\log\sigma-\log\rho_G,G;\sigma).$$
--
--   The first identity says that a stationarity test with the observable $H-G$ measures the Fisher information. The second, the second equality of (47) ([BCV25, Theorem B.1]), writes the Fisher information as a positive functional of commutators. Together they turn the gradient bound of Lemma 3.4 into the convexity bound of Lemma 3.3. They also let Lemma 5.4 bound the Fisher information of the completed guess by stationarity tests.
--
--   **Formalization Note** The Fisher information is the first expression of (47). Identity 1 is an equality of complex numbers, so the test is real there.
--
--   Differences from the source:
--   - generalization: single-site jumps a and the site sum i; Hamiltonians with |h_γ| ≤ 1 → every Pauli string a as a jump, and any real coefficients; reason: both identities hold for any self-adjoint Pauli jump and any real Hamiltonian; the source's cases are instances
--   - reading: "−d/dt D(e^{tL_{G,i}}[ρ_H] ∥ ρ_G)|_{t=0} := FI_{G,i}(ρ_H ∥ ρ_G)" → FI is the first expression of (47); the relative-entropy derivative is not restated; reason: (4) uses := to motivate the name; the paper's definition of FI is Definition 2.21
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Remark 1.3, (4), p.5; Definition 2.21, (47), p.18

import Definitions.Def_StationarityTest_Fisher

namespace StationarityTest

/-- **Remark 1.3**, (4), p.5, with **Definition 2.21**, (47), p.18 (Bergamaschi, *The
stationarity test*, arXiv:2610.01074, held file sha256 0b7e46fb…).

1. With the observable `O = H − G`, the stationarity test measures the Fisher information of
   `ρ_H` relative to `ρ_G`: `FI_{G,a}(ρ_H ∥ ρ_G) = β · Test_a[H − G, G; ρ_H]` for every Pauli
   jump `a`, and `FI_{G,i}(ρ_H ∥ ρ_G) = β · Test_i[H − G, G; ρ_H]` for every site `i` (4).
2. For every Pauli jump `a` and every full-rank state `σ`,
   `FI_{G,a}(σ ∥ ρ_G) = Q_a(log σ − log ρ_G, G; σ)` (the second equality of (47)).

**Formalization Note.** `FI` is the first expression of (47); the tests are complex numbers, and
clause 1 asserts equality in `ℂ` (so in particular the test is real). `H`, `G` have any real
coefficients on `S^k_[n]`. The derivative `−d/dt D(e^{tL}[ρ_H] ∥ ρ_G)` that (4) writes as a
definition (`:=`) is the paper's motivation and is not stated. -/
theorem remark_1_3 {n q k : ℕ} (h g : KLocal n q k → ℝ) {β : ℝ} (hβ : 0 < β) :
    ((∀ a : PauliString n q,
        ((fisherInfo (ham Finset.univ g) β a.mat (gibbs β (ham Finset.univ h)) : ℝ) : ℂ) =
          (β : ℂ) * testJump a β (ham Finset.univ h - ham Finset.univ g) (ham Finset.univ g)
            (gibbs β (ham Finset.univ h))) ∧
      ∀ i : Fin n,
        ((fisherSite (ham Finset.univ g) β i (gibbs β (ham Finset.univ h)) : ℝ) : ℂ) =
          (β : ℂ) * testSite i β (ham Finset.univ h - ham Finset.univ g) (ham Finset.univ g)
            (gibbs β (ham Finset.univ h))) ∧
    ∀ (a : PauliString n q) (σ : Op n q), IsFullRankState σ →
      fisherInfo (ham Finset.univ g) β a.mat σ =
        funcQ (ham Finset.univ g) β a.mat (logM σ - logM (gibbs β (ham Finset.univ g))) σ := by sorry

end StationarityTest
