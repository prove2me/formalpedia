-- Prove2me | Theorems.Thm_StationarityTest_Supplement_theorem_6_3
-- name    : StationarityTest.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:48:29.385071+00:00
-- url     : https://prove2.me/theorems/f5f7289c-865b-4f1e-9d00-298b51632cb8
-- title:
--   Theorem 6.3 — learning from $\varepsilon$-locally metastable states: $\max_\gamma|g_\gamma-h_\gamma|\le\eta$ for $\eta>c_\beta\varepsilon$, $c_\beta\le\beta^{-1}e^{\mathrm{poly}(\beta)}$
-- statement:
--   Fix integers $k,d,D\ge1$ and $c_{gr}\ge1$. There are constants $C>0$ and $K$ such that the following holds for every number of qubits $n\ge1$, inverse temperature $\beta>0$, accuracy $\eta>0$ and failure probability $\delta\in(0,1)$.
--
--   Let $\Gamma\subseteq S^k_{[n]}$ be a fixed set of interactions on $n$ qubits satisfying the $(d,D,c_{gr})$ condition, and put
--   $$
--   N:=C\,e^{C(1+\beta)^K}\,\beta^{-2}\,\eta^{-2}\Big(1+\log^+\frac{n}{\delta\eta}\Big)\Big(1+\log^+\frac1\eta\Big)^D,\qquad \log^+x=\max(0,\log x).
--   $$
--   There is a learning algorithm, depending on $n,\beta,\eta,\delta$ and $\Gamma$ only, that uses at most $N$ copies of its input state and at most $C(nN)^K$ quantum and classical processing time, with the following guarantee. Let $\varepsilon\in(0,1)$ with
--   $$
--   \eta>\eta_{thr}:=C\,\beta^{-1}e^{C(1+\beta)^K}\,\varepsilon,
--   $$
--   let $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ with $|h_\gamma|\le1$, and let $\sigma$ be any state that is $\varepsilon$-locally metastable with respect to $H$, i.e. $\|\mathcal L_{H,i}[\sigma]\|_1\le\varepsilon$ for every site $i$. Run on copies of $\sigma$, the algorithm outputs $G=\sum_{\gamma\in\Gamma}g_\gamma P_\gamma$ with
--   $$
--   \max_{\gamma\in\Gamma}|h_\gamma-g_\gamma|\le\eta
--   $$
--   with probability at least $1-\delta$.
--
--   The state $\sigma$ need not be close to the Gibbs state $\rho_H$: approximate stationarity under the local Gibbs-sampler generators suffices to learn the Hamiltonian, down to an accuracy plateau proportional to $\varepsilon$.
--
--   **Formalization Note** The learner is the base mission's `GibbsLearner` with the decoder `decodeBlocks`, exactly as in Theorem 4.1; it is fixed before $\varepsilon$, $h$ and $\sigma$.
--
--   Differences from the source:
--   - encoding: (d, D, c), k local qubit Hamiltonians, parameters fixed → q = 1; ∀ k d D ≥ 1, c_gr ≥ 1 ∃ C > 0, K, then ∀ n ≥ 1, β > 0, δ ∈ (0, 1); reason: §6, p.36; n ≥ 1 sites excludes only the empty system
--   - reading: η > η_thr := c_β · ε where c_β ≤ β⁻¹ · e^{poly(β)} → C β⁻¹ e^{C(1+β)^K} ε < η; reason: equivalent to the existence of such a c_β (a larger c_β only shrinks the range of η)
--   - reading: the learning algorithm described in Section 4 → ∃ one GibbsLearner chosen from n, β, η, δ and the known Γ, fixed before ε, h and σ, outputting g_γ for γ ∈ Γ via decodeBlocks; reason: Lemma 6.11: the algorithm's parameters depend only on β and the Hamiltonian parameters; the base mission's model of computation
--   - reading: N_samp = (e^{poly(β)}/β²) · O(η⁻² log(n/(δη)) · log^D(1/η)) (137), for every η > η_thr → copies ≤ C e^{C(1+β)^K} β⁻² η⁻² (1 + log⁺(n/(δη))) (1 + log⁺(1/η))^D for every η > 0 above the threshold, log⁺ x = max(0, log x); reason: for η < 1 this is the base mission's reading of (101); the theorem places no upper bound on η, and log⁺ keeps the printed factor meaningful for η ≥ 1, where log(1/η) ≤ 0
--   - reading: poly(n, N_samp) quantum and classical processing time → time ≤ C (n · N)^K with the same C, K; reason: a polynomial in n and N; equivalent to a polynomial bound for a large C
--   - encoding: σ an ε-locally metastable state w.r.t. H, |h_γ| ≤ 1, with probability ≥ 1 − δ → σ with IsDensityMatrix σ and IsLocallyMetastable (ham Γ h) β ε σ; |h_γ| ≤ 1 (γ ∈ Γ); successProb σ ≥ 1 − δ; reason: Definition 6.1; σ is not assumed full rank or related to ρ_H; the probability is over the learner's outcomes
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Theorem 6.3, (136)–(137), p.36 (§6.2–6.3, pp.41–48)

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Learner
import Definitions.Def_StationarityTest_Supplement_Metastable

namespace StationarityTest.Supplement

/-- **Theorem 6.3 (Learning from metastable states)**, p.36 (Bergamaschi, *The stationarity
test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Fix `β ∈ ℝ₊`, `ε ∈ (0, 1)`, an `n` site
`(d, D, c_gr)` Hamiltonian `H := Σ_{γ∈Γ} h_γ P_γ` on a fixed set of interactions `Γ` with
`|h_γ| ≤ 1`. Let `σ` be an `ε`-locally metastable state w.r.t. `H`. Fix `δ ∈ (0, 1)` and
`η > η_thr := c_β · ε` where `c_β ≤ β^{−1} · e^{poly(β)}`. Then, with probability `≥ 1 − δ`, the
learning algorithm described in Section 4 returns a Hamiltonian `G = Σ_{γ∈Γ} g_γ P_γ` satisfying
`max_{γ∈Γ} |h_γ − g_γ| ≤ η` using at most
`N_samp := (e^{poly(β)}/β²) · O(η^{−2} log(n/(δη)) · log^D(1/η))` (137) copies of `σ` and
`poly(n, N_samp)` quantum and classical processing time.

**Formalization Note.** Qubits, `q = 1` (§6, p.36: "k local qubit Hamiltonians"); `k, d, D ≥ 1`,
`c_gr ≥ 1` fixed and absorbed into the constants `∃ C > 0, K`. Then `∀ n ≥ 1, β > 0,
δ ∈ (0, 1), η > 0` and every `(d, D, c_gr)` clause set `Γ`, `∃` one learner — "the learning
algorithm described in Section 4" takes `η, δ` and the known `Γ`, its parameters depend only on
`β` and the Hamiltonian parameters (Lemma 6.11) — fixed before `ε`, `h` and `σ`. The threshold
`c_β ≤ β^{−1} e^{poly(β)}` is read as `η > C β^{−1} e^{C(1+β)^K} ε` (equivalent to the existence
of such a `c_β`). `σ` is any density matrix (not assumed full rank, not related to `ρ_H`) with
`‖L_{H,i}[σ]‖₁ ≤ ε` for every site `i` (`IsLocallyMetastable`). The copy bound is
`N := C e^{C(1+β)^K} β^{−2} η^{−2} (1 + log⁺(n/(δη))) (1 + log⁺(1/η))^D` with
`log⁺ x = max(0, log x)`: for `η < 1` this is the base mission's reading of (137)
(`log^D(1/η) ↦ (1 + log(1/η))^D`, `log(n/(δη)) ↦ 1 + log(n/(δη))`), and `log⁺` keeps the
printed bound meaningful for `η ≥ 1`, which the theorem also covers (only `η > η_thr` is
required). The time bound is `C (n · N)^K`, a polynomial in `n` and `N`. -/
theorem theorem_6_3 : ∀ k d D : ℕ, 1 ≤ k → 1 ≤ d → 1 ≤ D → ∀ cgr : ℝ, 1 ≤ cgr →
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
    ∀ n : ℕ, 1 ≤ n → ∀ β η δ : ℝ, 0 < β → 0 < η → 0 < δ → δ < 1 →
    ∀ Γ : Finset (KLocal n 1 k), IsDDcgr d D cgr Γ →
    ∃ len wp : ℕ, ∃ L : GibbsLearner (n * 1) (Γ.card * (len + 1)),
      (L.copiesUsed : ℝ) ≤ C * Real.exp (C * (1 + β) ^ K) * (β⁻¹) ^ 2 * (η⁻¹) ^ 2 *
        (1 + max 0 (Real.log (n / (δ * η)))) * (1 + max 0 (Real.log (1 / η))) ^ D ∧
      (L.time : ℝ) ≤ C * ((n : ℝ) * (C * Real.exp (C * (1 + β) ^ K) * (β⁻¹) ^ 2 * (η⁻¹) ^ 2 *
        (1 + max 0 (Real.log (n / (δ * η)))) * (1 + max 0 (Real.log (1 / η))) ^ D)) ^ K ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → C * β⁻¹ * Real.exp (C * (1 + β) ^ K) * ε < η →
      ∀ h : KLocal n 1 k → ℝ, (∀ γ ∈ Γ, |h γ| ≤ 1) →
      ∀ σ : Op n 1, QAlgorithms.IsDensityMatrix σ →
        IsLocallyMetastable (ham Γ h) β ε σ →
        1 - δ ≤ L.successProb σ (fun x =>
          ∀ γ : ↥Γ, |decodeBlocks Γ.equivFin len wp x γ - h γ| ≤ η) := by sorry

end StationarityTest.Supplement
