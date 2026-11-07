-- Prove2me | Theorems.Thm_StationarityTest_lemma_5_5
-- name    : StationarityTest.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:25:37.943278+00:00
-- url     : https://prove2.me/theorems/f5eb4c22-4c9d-469d-8806-4c39a5b1fe5a
-- title:
--   Lemma 5.5 — all perturbed stationarity tests to error $c_{\mathrm{meas}}\eta_r$ from $e^{\mathrm{poly}(\beta d)}O(\eta_r^{-2}\log^D\eta_r^{-1}\log(n/\delta))$ samples
-- statement:
--   Fix $q,k,d,D\ge1$, $c_{gr}\ge1$ and an exponent $K_0$. There are $C>0$ and $K$ such that the following holds. Let $n\ge1$ and $\beta d\ge1$. Let the algorithm parameters satisfy $1<\ell\le K_0(\beta d)^{K_0}$, $\kappa\in(0,1)$ and $c_{\mathrm{meas}}\le1$, with $\kappa,c_{\mathrm{meas}}\ge e^{-K_0(\beta d)^{K_0}}$. Let $r\ge0$, $\eta_r=2^{-r}$, $\delta\in(0,1)$, and let $G^{(r)}$ be any guess. Then there is a learner, which may depend on $G^{(r)}$ but is fixed before $H$, with the following properties.
--
--   1. It outputs a list of estimates labelled injectively by tuples $(i,\Lambda,U,P)$, covering every triple $(i,\Lambda,U)$ considered by Algorithm 3 and every $P\in S^k_{[n]}$.
--   2. It uses at most
--   $$N=C\,e^{C(\beta d)^K}\big(1+\log(1/\eta_r)\big)^D\eta_r^{-2}\big(1+\log(n/\delta)\big)$$
--   copies of $\rho_H$ and time at most $C\,n^{C(\beta d)^K}N^K$.
--   3. Let $H$ be any $(d,D,c_{gr})$ Hamiltonian with $|h_P|\le1$, $\max_P|g_P-h_P|\le\eta_r$ and $\Gamma_{G^{(r)}}\subseteq\Gamma_H$. With probability at least $1-\delta$, every estimate labelled by a considered tuple is within $c_{\mathrm{meas}}\eta_r$ of $|\mathrm{Test}_i[P,G^{(r)}+\eta_rU;\rho_H]|$.
--
--   Combined with Lemma 5.4 over $\lceil\log_21/\eta\rceil$ rounds, this gives the sample bound of Theorem 5.1, which is optimal in $\eta$ and $n$ up to the $\log^D$ factor.
--
--   Differences from the source:
--   - generalization: "the choice of algorithm parameters ℓ, κ, c_meas determined by Lemma 5.4" → every ℓ > 1, κ ∈ (0, 1), c_meas ∈ (0, 1] with ℓ ≤ K₀(βd)^{K₀} and κ, c_meas ≥ e^{−K₀(βd)^{K₀}}, the constants C, K depending on K₀; reason: the proofs of Lemmas 5.4 and 5.5 choose ℓ = poly(βd) and κ = c_meas = e^{−poly(βd)}, which lie in this range for some K₀; the e^{poly(βd)} of (122) absorbs them
--   - reading: "N_samp := e^{poly(βd)} · O(log^D η_r^{−1}/η_r² · log(n/δ))" → C e^{C(βd)^K} (1 + log(1/η_r))^D η_r^{−2} (1 + log(n/δ)); reason: at r = 0 the printed log^D(1/η_0) = 0, and at n = 1, δ → 1 log(n/δ) → 0, while any learner that depends on ρ_H uses a copy; the 1 + log forms are the uniform versions of the asymptotic bound
--   - reading: "Recall the context of Algorithm 3 … G^(r) … accurate to error η_r" → hypotheses on H: (d, D, c_gr), |h_P| ≤ 1, max_P |g_P − h_P| ≤ η_r and Γ_{G^(r)} ⊆ Γ_H (the invariant (107)); reason: the context the lemma recalls
--   - encoding: "outputs estimates for (121) for every i, Λ, U, P" → an injective labelling lab of the outputs that covers every considered (i, Λ, U) and every P; accuracy is required at considered labels; reason: Grid(Λ) is a set of real vectors; the labelling indexes the finite family without a finiteness proof, and injectivity forbids several guesses for one tuple
--   - reading: "there exists an algorithm", "time n^{poly(βd)} · poly(N_samp)" → a GibbsLearner on copies of ρ_H, time ≤ C n^{C(βd)^K} N^K; reason: the mission's model of computation (StationarityTest.Learner)
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Lemma 5.5, (121)–(122), p.32 (proof pp.34–35, Algorithm 4)

import Definitions.Def_StationarityTest_Algorithm
import Definitions.Def_StationarityTest_Learner

namespace StationarityTest

/-- **Lemma 5.5 (Parallel measurements of the stationarity test)**, p.32 (Bergamaschi, *The
stationarity test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Fix `β ≥ d^{−1}`. In the
context of Algorithm 3, with the algorithm parameters `ℓ, κ, c_meas` of Lemma 5.4, let `G^(r)` be
the guess after the `r`-th iteration, accurate to `η_r`. There is an algorithm which with
probability `≥ 1 − δ` outputs estimates of `|Test_i[P, G^(r) + η_r U; ρ_H]|` (121) for every
`i ∈ [n]`, `Λ ∈ CC_{i,ℓ}`, `U ∈ Grid(Λ)` and `P ∈ S^k_[n]` to error `c_meas η_r`, using
`N_samp := e^{poly(βd)} · O(log^D(η_r^{−1}) / η_r² · log(n/δ))` (122) samples of `ρ_H`, in
classical and quantum time `n^{poly(βd)} · poly(N_samp)`.

**Formalization Note.** The parameters of Lemma 5.4 satisfy `ℓ = poly(βd)` and
`κ, c_meas ≥ e^{−poly(βd)}` (proof of Lemma 5.4, p.31; proof of Lemma 5.5, p.34); the statement
holds for every `ℓ > 1`, `κ ∈ (0, 1)`, `c_meas ∈ (0, 1]` with `ℓ ≤ K₀ (βd)^{K₀}` and
`κ, c_meas ≥ e^{−K₀(βd)^{K₀}}`, the constants `C, K` depending on `q, k, d, D, c_gr, K₀`. The
learner may depend on `G^(r)` (the algorithm knows it) and is fixed before `H`. It outputs `M`
estimates, the `j`-th labelled `lab j = (i, Λ, U, P)`; `lab` is injective and covers every triple
considered by Algorithm 3 and every `P`. Bounds: copies
`≤ C e^{C(βd)^K} (1 + log(1/η_r))^D η_r^{−2} (1 + log(n/δ))`, time `≤ C n^{C(βd)^K} N^K`, with
`η_r = 2^{−r}`; `log^D` and `log(n/δ)` are read as `(1 + log)^D` and `1 + log(n/δ)` (at `r = 0`,
`n = 1`, `δ → 1` the printed bound vanishes). The context of Algorithm 3: `H` a
`(d, D, c_gr)` Hamiltonian with `|h_P| ≤ 1`, `max_P |g^(r)_P − h_P| ≤ η_r` and
`Γ_{G^(r)} ⊆ Γ_H` (the invariant (107)). -/
theorem lemma_5_5 : ∀ q k d D : ℕ, 1 ≤ q → 1 ≤ k → 1 ≤ d → 1 ≤ D → ∀ cgr : ℝ, 1 ≤ cgr →
    ∀ K₀ : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
    ∀ n : ℕ, 1 ≤ n → ∀ β : ℝ, 1 ≤ β * d →
    ∀ (ℓ : ℕ) (κ cmeas : ℝ), 1 < ℓ → (ℓ : ℝ) ≤ K₀ * (β * d) ^ K₀ → 0 < κ → κ < 1 →
    Real.exp (-(K₀ * (β * d) ^ K₀)) ≤ κ → Real.exp (-(K₀ * (β * d) ^ K₀)) ≤ cmeas → cmeas ≤ 1 →
    ∀ (r : ℕ) (δ : ℝ), 0 < δ → δ < 1 → ∀ g : KLocal n q k → ℝ,
    ∃ M : ℕ, ∃ lab : Fin M → Fin n × Finset (KLocal n q k) × (KLocal n q k → ℝ) × KLocal n q k,
      Function.Injective lab ∧
      (∀ i Λ U P, Considered ℓ d D cgr κ g i Λ U → ∃ j, lab j = (i, Λ, U, P)) ∧
      ∃ len wp : ℕ, ∃ L : GibbsLearner (n * q) (M * (len + 1)),
        (L.copiesUsed : ℝ) ≤ C * Real.exp (C * (β * d) ^ K) *
          (1 + Real.log ((2 : ℝ) ^ r)) ^ D * ((2 : ℝ) ^ r) ^ 2 * (1 + Real.log (n / δ)) ∧
        (L.time : ℝ) ≤ C * (n : ℝ) ^ (C * (β * d) ^ K) *
          (C * Real.exp (C * (β * d) ^ K) * (1 + Real.log ((2 : ℝ) ^ r)) ^ D * ((2 : ℝ) ^ r) ^ 2 *
            (1 + Real.log (n / δ))) ^ K ∧
        ∀ h : KLocal n q k → ℝ, (∀ P, |h P| ≤ 1) → IsDDcgr d D cgr (coeffSupport h) →
          (∀ P, |g P - h P| ≤ ((2 : ℝ) ^ r)⁻¹) → (∀ P, g P ≠ 0 → h P ≠ 0) →
          1 - δ ≤ L.successProb (gibbs β (ham Finset.univ h)) (fun x => ∀ j : Fin M,
            Considered ℓ d D cgr κ g (lab j).1 (lab j).2.1 (lab j).2.2.1 →
            |decodeBlocks (Equiv.refl (Fin M)) len wp x j -
              ‖testSite (lab j).1 β (lab j).2.2.2.1.mat
                (ham Finset.univ fun Q => g Q + ((2 : ℝ) ^ r)⁻¹ * (lab j).2.2.1 Q)
                (gibbs β (ham Finset.univ h))‖| ≤ cmeas * ((2 : ℝ) ^ r)⁻¹) := by sorry

end StationarityTest
