-- Prove2me | Theorems.Thm_StationarityTest_theorem_5_1
-- name    : StationarityTest.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:02.446215+00:00
-- url     : https://prove2.me/theorems/9a87ee12-7d6c-4fcb-8242-03f83e159c73
-- title:
--   Theorem 5.1 — structure learning: $\Gamma_G\subseteq\Gamma_H$ and $|g_P-h_P|\le\eta$ from $\frac{e^{\mathrm{poly}(\beta)}}{\beta^2}O(\eta^{-2}\log\frac n{\delta\eta}\log^D\frac1\eta)$ copies
-- statement:
--   Fix $q,k,d,D\ge1$ and $c_{gr}\ge1$. There are $C>0$ and $K\in\mathbb N$ such that the following holds. Let $n\ge1$, $\beta>0$ and $\eta,\delta\in(0,1)$. There is a learner, fixed before the Hamiltonian, that uses at most
--
--   $$N=C\,e^{C(1+\beta)^K}\,\beta^{-2}\,\eta^{-2}\Big(1+\log\frac n{\delta\eta}\Big)\Big(1+\log\frac1\eta\Big)^D$$
--
--   copies of the Gibbs state and runs in time at most $C\,n^{C(1+\beta)^K}N^K$. It has the following guarantee. Let $H=\sum_{P\in S^k_{[n]}}h_PP$ be any $n$-qudit $(d,D,c_{gr})$ Hamiltonian with $|h_P|\le1$, given only through copies of $\rho_H$. With probability at least $1-\delta$ the learner outputs coefficients $(g_P)_{P\in S^k_{[n]}}$ with
--
--   $$\Gamma_G\subseteq\Gamma_H\qquad\text{and}\qquad|g_P-h_P|\le\eta\ \text{ for every }P\in S^k_{[n]}.$$
--
--   This is structure learning: neither the interaction graph nor the coefficients of $H$ are known. The guarantee holds at every inverse temperature $\beta$. The sample count is quadratic in $1/\eta$ and logarithmic in $n$.
--
--   **Formalization Note** The learner is the mission's model of computation (`StationarityTest.Learner`), and its output is read by the fixed dyadic decoder, one block per $P\in S^k_{[n]}$. $\Gamma_G\subseteq\Gamma_H$ means $g_P\ne0\Rightarrow h_P\ne0$. The constants $C,K$ depend only on $q,k,d,D,c_{gr}$. The copies and time do not depend on $H$.
--
--   Differences from the source:
--   - reading: "there exists an algorithm … uses at most N_samp samples of ρ_H, and at most poly(N_samp)·n^{poly(β)} processing time" → ∃ a GibbsLearner (rounds on fresh copies, {H, T, CNOT} circuits, classical control by Boolean circuits, computational-basis measurement), fixed before H, with copiesUsed ≤ N and time ≤ C n^{C(1+β)^K} N^K; reason: the paper names no model of computation; this is the published CopyLearner model for mixed states, and an algorithm that outputs a Hamiltonian must be fixed before it
--   - encoding: "e^{poly(β)}", "poly(N_samp)", "n^{poly(β)}", O(·) with d, D, c_gr, k, q fixed → ∀ q, k, d, D, c_gr ∃ C > 0, K, then ∀ n, β, η, δ: e^{C(1+β)^K}, C N^K, n^{C(1+β)^K}; reason: p.14 and p.28: the Hamiltonian parameters are fixed constants absorbed into O(·), and n, η, δ, β scale
--   - reading: "log^D(1/η)" → (1 + log(1/η))^D; reason: as η → 1 the printed factor tends to 0 while one round needs copies; the O(·) is asymptotic as η → 0, where the two agree up to the factor 2^D for η ≤ 1/e
--   - reading: "log(n/(δ·η))" → 1 + log(n/(δη)); reason: at n = 1 and δη → 1 the printed factor tends to 0, while a learner with no copies has a fixed output and fails for some H (h = 0 forces g = 0, then h_X = 1 is missed); 1 + log is the uniform form of the asymptotic bound
--   - encoding: "with probability 1 − δ" → with probability at least 1 − δ; reason: the standard meaning
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Theorem 5.1, (100)–(101), p.28 (proof p.33; Remark 4.5, p.27)

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Learner

namespace StationarityTest

/-- **Theorem 5.1 (Structure learning from Gibbs states)**, p.28 (Bergamaschi, *The stationarity
test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Let `η, δ ∈ (0, 1)`, `β > 0` and let `H`
be an `n`-qudit `(d, D, c_gr)` Hamiltonian. There is an algorithm which, with probability
`1 − δ`, outputs a Hamiltonian `G = Σ_{P∈S^k_[n]} g_P P` with `Γ_G ⊆ Γ_H` and
`|g_P − h_P| ≤ η` for all `P ∈ S^k_[n]`. It uses at most
`N_samp := (e^{poly(β)}/β²) O(η^{−2} log(n/(δη)) log^D(1/η))` (101) samples of `ρ_H` and at most
`poly(N_samp) · n^{poly(β)}` processing time.

**Formalization Note.** `H = Σ_{P∈S^k_[n]} h_P P` with `|h_P| ≤ 1` and `Γ_H = {P : h_P ≠ 0}`
(100), `(d, D, c_gr)` on `Γ_H` (Definition 2.2); `q, k, d, D ≥ 1`, `c_gr ≥ 1` are fixed and
absorbed into the constants: `∀ q, k, d, D, c_gr ∃ C > 0, K`, then `∀ n ≥ 1, β > 0,
η, δ ∈ (0, 1) ∃` a learner, then `∀ H` (the learner is fixed before `H`; copies and time do not
depend on `H`). The learner (`GibbsLearner`, the model of `QAlgorithms.CopyLearner` for mixed
states) outputs a dyadic coefficient for every `P ∈ S^k_[n]` through the fixed decoder
`decodeBlocks`. With `e^{poly(β)} = e^{C(1+β)^K}` and `poly(N_samp) = C N^K`, the bounds are
`copies ≤ N := C e^{C(1+β)^K} β^{−2} η^{−2} (1 + log(n/(δη))) (1 + log(1/η))^D` and
`time ≤ C n^{C(1+β)^K} N^K`. Readings: `log^D(1/η)` is `(1 + log(1/η))^D` (the printed factor
tends to `0` as `η → 1` while one round needs copies) and `log(n/(δη))` is `1 + log(n/(δη))`
(at `n = 1`, `δη → 1` the printed factor tends to `0`, while a learner that uses no copies has a
fixed output and fails for some `H`). "With probability `1 − δ`" means at least `1 − δ`.
`Γ_G ⊆ Γ_H` is `g_P ≠ 0 → h_P ≠ 0`. -/
theorem theorem_5_1 : ∀ q k d D : ℕ, 1 ≤ q → 1 ≤ k → 1 ≤ d → 1 ≤ D → ∀ cgr : ℝ, 1 ≤ cgr →
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
    ∀ n : ℕ, 1 ≤ n → ∀ β η δ : ℝ, 0 < β → 0 < η → η < 1 → 0 < δ → δ < 1 →
    ∃ len wp : ℕ, ∃ L : GibbsLearner (n * q) (Fintype.card (KLocal n q k) * (len + 1)),
      (L.copiesUsed : ℝ) ≤ C * Real.exp (C * (1 + β) ^ K) * (β⁻¹) ^ 2 * (η⁻¹) ^ 2 *
        (1 + Real.log (n / (δ * η))) * (1 + Real.log (1 / η)) ^ D ∧
      (L.time : ℝ) ≤ C * (n : ℝ) ^ (C * (1 + β) ^ K) *
        (C * Real.exp (C * (1 + β) ^ K) * (β⁻¹) ^ 2 * (η⁻¹) ^ 2 *
          (1 + Real.log (n / (δ * η))) * (1 + Real.log (1 / η)) ^ D) ^ K ∧
      ∀ h : KLocal n q k → ℝ, (∀ P, |h P| ≤ 1) → IsDDcgr d D cgr (coeffSupport h) →
        1 - δ ≤ L.successProb (gibbs β (ham Finset.univ h)) (fun x =>
          (∀ P, decodeBlocks (Fintype.equivFin (KLocal n q k)) len wp x P ≠ 0 → h P ≠ 0) ∧
          ∀ P, |decodeBlocks (Fintype.equivFin (KLocal n q k)) len wp x P - h P| ≤ η) := by sorry

end StationarityTest
