-- Prove2me | Theorems.Thm_SYKLearn_theorem_1_1
-- name    : SYKLearn.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:11.615197+00:00
-- url     : https://prove2.me/theorems/f219508e-1a72-44dd-b1b8-084af297bbab
-- title:
--   Theorem 1.1 — SYK couplings to normalized error $\varepsilon$ from $\mathrm{poly}(b^{-1},2^{\beta^2},n,1/\varepsilon,\log(1/\delta))$ Gibbs-state copies and time, at every $\beta>0$
-- statement:
--   Let $H_g=\sum_{|I|=4}g_I\Gamma_I$ be the SYK Hamiltonian on $n$ Majorana modes with $g_I\sim\mathcal N(0,\sigma_n^2)$, $\sigma_n^2=6/n^3$, $m=\binom n4$. There are universal constants $C>0$ and $K$ such that the following holds. Fix any inverse temperature $\beta>0$ and write $b=\min\{\beta,1\}$. There are $C_\beta$ and $N_0(\beta)$ such that for every even $n\ge N_0(\beta)$ there is a set $G$ of coupling vectors with $\Pr_g[g\notin G]\le C_\beta/n$, and for every $\varepsilon,\delta\in(0,1/2)$ there is a quantum algorithm which, given independent copies of the physical Gibbs state $e^{-\beta H_g}/\mathrm{tr}[e^{-\beta H_g}]$,
--
--   1. uses at most $C\,(b^{-1}2^{\beta^2}n\,\varepsilon^{-1}\log(1/\delta))^K$ copies,
--   2. runs in time at most $C\,(b^{-1}2^{\beta^2}n\,\varepsilon^{-1}\log(1/\delta))^K$, and
--   3. for every $g\in G$, with probability at least $1-\delta$ over the algorithm, outputs estimates $\hat g_I$ with
--   $$\frac{1}{\sigma_n^2\binom n4}\sum_{I\in\binom{[n]}4}(\hat g_I-g_I)^2\le\varepsilon .$$
--
--   This is the first polynomial-time algorithm that learns the couplings of the dense quartic SYK model to arbitrary accuracy from thermal states at every fixed temperature, with no high-temperature assumption.
--
--   **Formalization Note** The algorithm is a learner in the published copy-learner model (adaptive rounds on fresh copies, $\{H,T,\mathrm{CNOT}\}$ gates with Boolean classical control, computational-basis measurements; time counts gates, ancillas and Boolean gates), fixed before the couplings and given only copies of the state. Its output bits are read as dyadic numbers $\hat g_I$ by a fixed decoder. The Majoranas are the Jordan–Wigner operators on $n/2$ qubits. $2^{\beta^2}$ is a real power.
--
--   Differences from the source:
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − x over g → the complement of the good set has (outer) measure at most x; reason: equivalent for measurable events, and no measurability of the event is assumed
--   - encoding: Majorana operators on the qubit register used by the algorithm (Jordan–Wigner, Lemma 4.9, p.39; §5, p.43) → hypothesis ∀ i, Q.γ i = jw Q i, and the learner receives toReg of the physical Gibbs state; reason: gate counts depend on the representation; the paper's circuits use the Jordan–Wigner encoding, and jw is a CAR family (proved in the sanity file)
--   - reading: poly(b⁻¹, 2^{β²}, n, 1/ε, log(1/δ)) copies and time → ∃ C > 0, K chosen before β, with copies ≤ C·(b⁻¹·2^{β²}·n·ε⁻¹·log(1/δ))^K and time ≤ the same; reason: a polynomial in b⁻¹ and 2^{β²} as variables cannot depend on β; this is the stronger reading, and every polynomial in these variables is so bounded since all but log(1/δ) > log 2 are ≥ 1
--   - reading: “for all but an O_β(1/n) fraction of SYK Hamiltonians” (placed after “for every ε, δ”) → one set G with measure of Gᶜ ≤ C_β/n, chosen before ε, δ; reason: the proof's event (Theorem 3.1's E_dir and Lemma 4.6's event) depends on g only; this is the stronger reading
--   - reading: “there is a quantum algorithm that … uses … copies … runs in time …” (no model of computation named) → a StationarityTest.GibbsLearner on the N/2-qubit register, chosen before the coupling, given copies of toReg of the physical Gibbs state, its output decoded by decodeBlocks; reason: the platform's copy-learner model for mixed states; phase estimation, Trotterization, measurement of Γ_J and finite-precision SVD all run inside it
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Theorem 1.1, p.3 (restated p.41; proof pp.41–43)

import Mathlib
import Definitions.Def_SYKLearn_Basic
import Definitions.Def_StationarityTest_Learner

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Theorem 1.1 (Efficient learning of SYK Hamiltonians from Gibbs state access)**, p.3 (restated
p.41) (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission, held file sha256 5d7d199a…). Fix any inverse temperature `β > 0`. Write
`b = min{β, 1}`. For every sufficiently large even `n` depending on `β`, consider the SYK
Hamiltonian `H_g`. For every `ε, δ ∈ (0, 1/2)`, there is a quantum algorithm that, given
independent copies of the physical Gibbs state `2^{−n/2}ρ_β = e^{−βH_g}/tr[e^{−βH_g}]`, uses
`poly(b^{−1}, 2^{β²}, n, 1/ε, log(1/δ))` copies of `ρ_β`, runs in time
`poly(b^{−1}, 2^{β²}, n, 1/ε, log(1/δ))`, and outputs estimates `ĝ_I` satisfying
`(1/(σ_n² C(n,4))) Σ_{I} (ĝ_I − g_I)² ≤ ε`. The guarantee holds with probability `≥ 1 − δ` over the
algorithm, for all but an `O_β(1/n)` fraction of SYK Hamiltonians.

**Formalization Note.**
* The polynomial is universal: `C, K` are chosen before `β`, and both the copy count and the time
  are bounded by `C·(b^{−1}·2^{β²}·n·ε^{−1}·log(1/δ))^K` (every polynomial in these variables is
  so bounded, since each variable but `log(1/δ) > log 2` is `≥ 1`). `2^{β²}` is `Real.rpow`.
* "For all but an `O_β(1/n)` fraction": a set `G` of couplings, chosen after `β, n` and before
  `ε, δ`, whose complement has measure `≤ C_β/n` (outer measure, no measurability assumed).
* The algorithm is a learner in the published model `StationarityTest.GibbsLearner` on the
  `N/2`-qubit register (adaptive rounds on fresh copies, `{H, T, CNOT}` gates with Boolean classical
  control, computational-basis measurements, Boolean output circuit; `time` counts gates,
  ancillas and Boolean gates). It is chosen after `β, n, G, ε, δ` and before the coupling `w`, and
  receives only copies of the physical Gibbs state `toReg (gibbs (hamiltonian Q w) β)`. Its output
  bits are read by the fixed dyadic decoder `decodeBlocks` as the estimates `ĝ_I`.
* The Majoranas are pinned to Jordan–Wigner (`Q.γ = jw Q`), the encoding the paper's circuits use
  (Lemma 4.9, p.39), because gate counts depend on the representation. `Q.J = 1` makes the
  couplings `N(0, 6/n³)`; `n` even and `n ≥ 4` come from `Model`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ β : ℝ, 0 < β → ∃ Cβ : ℝ, ∃ N₀ : ℕ,
      ∀ (N : ℕ) (Q : Model N), N₀ ≤ N → Q.J = 1 → (∀ i, Q.γ i = jw Q i) →
        ∃ G : Set (Disorder N), disorderLaw Q Gᶜ ≤ ENNReal.ofReal (Cβ / N) ∧
          ∀ ε δ : ℝ, 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
            ∃ len wp : ℕ, ∃ L : StationarityTest.GibbsLearner (N / 2) (m N * (len + 1)),
              (L.copiesUsed : ℝ) ≤
                C * ((min β 1)⁻¹ * (2 : ℝ) ^ (β ^ 2) * N * ε⁻¹ * Real.log (1 / δ)) ^ K ∧
              (L.time : ℝ) ≤
                C * ((min β 1)⁻¹ * (2 : ℝ) ^ (β ^ 2) * N * ε⁻¹ * Real.log (1 / δ)) ^ K ∧
              ∀ w ∈ G, 1 - δ ≤ L.successProb (toReg (gibbs (hamiltonian Q w) β))
                (fun x => (sigma N ^ 2 * m N)⁻¹ *
                  ∑ I, (StationarityTest.decodeBlocks (Fintype.equivFin (SYKEdge.KSet N 4))
                    len wp x I - w I) ^ 2 ≤ ε) := by sorry

end SYKLearn
