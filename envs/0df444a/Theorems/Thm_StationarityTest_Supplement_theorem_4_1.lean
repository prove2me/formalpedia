-- Prove2me | Theorems.Thm_StationarityTest_Supplement_theorem_4_1
-- name    : StationarityTest.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:47:50.08421+00:00
-- url     : https://prove2.me/theorems/cadbf131-b3d6-483d-b95a-514146cae901
-- title:
--   Theorem 4.1 — known interaction set: $\max_\gamma|g_\gamma-h_\gamma|\le\eta$ from $\tilde O(e^{\mathrm{poly}(\beta)}\beta^{-2}\eta^{-2}\log n)$ Gibbs copies in $\mathrm{poly}(n,N)$ time
-- statement:
--   Fix integers $q,k,d,D\ge1$ and $c_{gr}\ge1$. There are constants $C>0$ and $K$ such that the following holds for every $n\ge1$, inverse temperature $\beta>0$, accuracy $\eta\in(0,1)$ and failure probability $\delta\in(0,1)$.
--
--   Let $\Gamma\subseteq S^k_{[n]}$ be a known set of interactions whose interaction graph satisfies the $(d,D,c_{gr})$ condition (Definition 2.2), on $n$ qudits of $q$ qubits each. Put
--   $$
--   N:=C\,e^{C(1+\beta)^K}\,\beta^{-2}\,\eta^{-2}\Big(1+\log\frac{n}{\delta\eta}\Big)\Big(1+\log\frac1\eta\Big)^D .
--   $$
--   There is a quantum learning algorithm, depending on $n,\beta,\eta,\delta$ and $\Gamma$ but not on the coefficients, that uses at most $N$ copies of its input state and at most $C(nN)^K$ quantum and classical processing time, such that for every Hamiltonian $H=\sum_{\gamma\in\Gamma}h_\gamma P_\gamma$ with $|h_\gamma|\le1$, run on copies of the Gibbs state $\rho_H=e^{-\beta H}/\operatorname{tr}e^{-\beta H}$, it outputs $G=\sum_{\gamma\in\Gamma}g_\gamma P_\gamma$ with
--   $$
--   \max_{\gamma\in\Gamma}|h_\gamma-g_\gamma|\le\eta
--   $$
--   with probability at least $1-\delta$.
--
--   This is the known-structure warm-up of the stationarity-test framework, recovering the parameter-learning results of [BLMT23; CAN25]. Its running time is polynomial in $n$ with an exponent independent of $\beta$, which the structure-learning Theorem 5.1 does not give.
--
--   **Formalization Note** The learner is the base mission's `GibbsLearner`: adaptive rounds on fresh copies of the state and ancillas, circuits over $\{H,T,\mathrm{CNOT}\}$ switched by Boolean control computed from earlier outcomes, computational-basis measurements, and a Boolean output circuit; time counts gates, ancillas and Boolean gates. Each $g_\gamma$ is a dyadic number written in a block of output bits.
--
--   Differences from the source:
--   - encoding: d, D, c_gr, q, k fixed constants; asymptotics in n, η, δ, β → ∀ q k d D ≥ 1, c_gr ≥ 1 ∃ C > 0, K, then ∀ n ≥ 1, β > 0, η, δ ∈ (0, 1); reason: p.23 'we treat the Hamiltonian parameters d, D, cgr, q, k as fixed constants'; n ≥ 1 sites excludes only the empty system
--   - reading: Algorithms 1 and 2 return G … using … copies and … time → ∃ a GibbsLearner (rounds of copies of ρ_H, {H, T, CNOT} circuits, Boolean control), chosen from n, β, η, δ and the known Γ but fixed before h, outputting g_γ for γ ∈ Γ via decodeBlocks; reason: the base mission's model of computation for Theorem 5.1; Γ is an input ('known'), h is not
--   - reading: N_samples = (e^{poly(β)}/β²) · O(η⁻² log(n/(δη)) log^D(1/η)) → copies ≤ C e^{C(1+β)^K} β⁻² η⁻² (1 + log(n/(δη))) (1 + log(1/η))^D; reason: the base mission's reading of (101) (decision 5): the printed log factors vanish as δη → 1 or η → 1 while the learner needs copies
--   - reading: poly(n, N_samples) quantum and classical processing time → time ≤ C (n · N)^K with the same C, K; reason: a polynomial in n and N whose exponent does not depend on β (unlike Theorem 5.1's n^{poly(β)}); n ≥ 1 and N ≥ 1 for a large C, so this is equivalent to a polynomial bound
--   - encoding: H := Σ_{γ∈Γ} h_γ P_γ a (d, D, c_gr) Hamiltonian; with probability ≥ 1 − δ → ham Γ h with IsDDcgr d D cgr Γ and |h_γ| ≤ 1 (γ ∈ Γ); successProb (gibbs β (ham Γ h)) ≥ 1 − δ; reason: (21) and Definition 2.2; the probability is over the learner's measurement outcomes
-- source:
--   Bergamaschi, The stationarity test: a framework for learning quantum many-body systems from their thermal states, arXiv:2610.01074 (held file sha256 0b7e46fb…), Theorem 4.1, (73), p.23 (Algorithms 1–2, pp.23–24; §4.2–4.3, pp.24–28)

import Definitions.Def_StationarityTest_Geometry
import Definitions.Def_StationarityTest_Learner

namespace StationarityTest.Supplement

/-- **Theorem 4.1 (Learning Hamiltonians from their Gibbs states)**, p.23 (Bergamaschi, *The
stationarity test*, arXiv:2610.01074, held file sha256 0b7e46fb…). Let `H := Σ_{γ∈Γ} h_γ P_γ` be
a `(d, D, c_gr)` Hamiltonian on a known set of interactions `Γ`. For any `η, δ ∈ (0, 1)`,
`β ∈ ℝ₊`, with probability `≥ 1 − δ`, Algorithms 1 and 2 return a Hamiltonian
`G = Σ_{γ∈Γ} g_γ P_γ` satisfying `max_{γ∈Γ} |h_γ − g_γ| ≤ η` using at most
`N_samples := (e^{poly(β)}/β²) · O(η^{−2} log(n/(δη)) log^D(1/η))` (73) copies of the Gibbs state
`ρ_H` and `poly(n, N_samples)` quantum and classical processing time.

**Formalization Note.** `q, k, d, D ≥ 1`, `c_gr ≥ 1` are fixed (p.23, "we treat the Hamiltonian
parameters d, D, c_gr, q, k as fixed constants") and absorbed into the constants:
`∀ q, k, d, D, c_gr ∃ C > 0, K`, then `∀ n ≥ 1, β > 0, η, δ ∈ (0, 1)` and every clause set
`Γ ⊆ S^k_[n]` satisfying the `(d, D, c_gr)` condition (Definition 2.2) `∃` one learner, which may
depend on `Γ` (it is known) but is fixed before the coefficients `h` (`|h_γ| ≤ 1`, (21)).
"Algorithms 1 and 2" is stated as existence of a learner with the printed resources and
guarantee, as in the published Theorem 5.1. The learner is the published `GibbsLearner`; it
writes one dyadic estimate `g_γ` per `γ ∈ Γ`, read by `decodeBlocks` along `Γ.equivFin`.
With `e^{poly(β)} = e^{C(1+β)^K}` and the base mission's readings
`log^D(1/η) ↦ (1 + log(1/η))^D`, `log(n/(δη)) ↦ 1 + log(n/(δη))`, the copy bound is
`N := C e^{C(1+β)^K} β^{−2} η^{−2} (1 + log(n/(δη))) (1 + log(1/η))^D`, and the time bound is
`C (n · N)^K`, a polynomial in `n` and `N` whose exponent does not depend on `β`. -/
theorem theorem_4_1 : ∀ q k d D : ℕ, 1 ≤ q → 1 ≤ k → 1 ≤ d → 1 ≤ D →
    ∀ cgr : ℝ, 1 ≤ cgr →
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ,
    ∀ n : ℕ, 1 ≤ n → ∀ β η δ : ℝ, 0 < β → 0 < η → η < 1 → 0 < δ → δ < 1 →
    ∀ Γ : Finset (KLocal n q k), IsDDcgr d D cgr Γ →
    ∃ len wp : ℕ, ∃ L : GibbsLearner (n * q) (Γ.card * (len + 1)),
      (L.copiesUsed : ℝ) ≤ C * Real.exp (C * (1 + β) ^ K) * (β⁻¹) ^ 2 * (η⁻¹) ^ 2 *
        (1 + Real.log (n / (δ * η))) * (1 + Real.log (1 / η)) ^ D ∧
      (L.time : ℝ) ≤ C * ((n : ℝ) * (C * Real.exp (C * (1 + β) ^ K) * (β⁻¹) ^ 2 * (η⁻¹) ^ 2 *
        (1 + Real.log (n / (δ * η))) * (1 + Real.log (1 / η)) ^ D)) ^ K ∧
      ∀ h : KLocal n q k → ℝ, (∀ γ ∈ Γ, |h γ| ≤ 1) →
        1 - δ ≤ L.successProb (gibbs β (ham Γ h)) (fun x =>
          ∀ γ : ↥Γ, |decodeBlocks Γ.equivFin len wp x γ - h γ| ≤ η) := by sorry

end StationarityTest.Supplement
