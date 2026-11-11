-- Prove2me | Theorems.Thm_SYKLearn_theorem_3_1
-- name    : SYKLearn.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:16:03.516949+00:00
-- url     : https://prove2.me/theorems/64d4427f-ea8b-41b7-8fa7-1e6f2d5748d6
-- title:
--   Theorem 3.1 — direction recovery: $\|\hat d-g/\|g\|_2\|_2\le\eta$ from $C_\beta n^{18}\max\{\eta^{-2},m^2\}\log(n/\delta)$ copies
-- statement:
--   Fix $\beta>0$. There are constants $C_\beta,n_0(\beta)>0$, and constants $C'_\beta,K_\beta$ for the running time, such that for every even $n\ge n_0(\beta)$ there is a set $G$ of coupling vectors of probability at least $1-C_\beta/n$ with the following property. For every $\eta,\delta\in(0,1/2)$ there is a quantum algorithm which, given independent copies of the physical Gibbs state $e^{-\beta H_g}/\mathrm{tr}[e^{-\beta H_g}]$,
--
--   1. uses at most $C_\beta\,n^{18}\max\{\eta^{-2},m^2\}\log(n/\delta)$ copies,
--   2. runs in time at most $C'_\beta\,(n\,\eta^{-1}\log(1/\delta))^{K_\beta}$, and
--   3. for every $g\in G$ returns a real unit vector $\hat d$ with
--   $$\Pr_{\rm alg}\Big[\big\|\hat d-d\big\|_2\le\eta\ \Big|\ g\Big]\ge1-\delta,\qquad d=\frac{g}{\|g\|_2}.$$
--
--   The algorithm estimates the direction matrix $M_\beta$ from measurements of degree-$4$ and degree-$8$ Majorana monomials and reads off its approximate null vector; the gap of Lemma 3.2 makes this stable, and the thermal energy fixes the sign.
--
--   **Formalization Note** The algorithm is fixed after $\beta,n,G,\eta,\delta$ and before the coupling vector, and sees only copies of the state. The output bits are read as a real vector $v$ by the fixed dyadic decoder and $\hat d=v/\|v\|_2$. "Time polynomial in $n,1/\eta,\log(1/\delta)$" is written as $C'(n\eta^{-1}\log(1/\delta))^K$, which is equivalent since $n\ge1$, $\eta^{-1}>2$ and $\log(1/\delta)>\log2$. The same $C_\beta$ bounds the exceptional probability and the copies, as on the page.
--
--   Differences from the source:
--   - encoding: g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − x over g → the complement of the good set has (outer) measure at most x; reason: equivalent for measurable events, and no measurability of the event is assumed
--   - reading: “Algorithm 3 uses … copies and time … and returns a real unit vector d̂” (Algorithm 3 is not given at gate level, p.33) → there is a learner L in the published StationarityTest.GibbsLearner model (adaptive rounds on fresh copies of the physical Gibbs state, {H, T, CNOT} gates with Boolean classical control, computational-basis measurement, Boolean output circuit; time = gates + ancillas + Boolean gates), chosen before the coupling; its output bits are decoded by decodeBlocks into v and d̂ = v/‖v‖ (v ≠ 0 required); reason: the paper names no model of computation; this is the platform's copy-learner model, inside which measurement of Γ_J, phase estimation, Trotterization and finite-precision SVD are all implementable
--   - encoding: Majorana operators on the qubit register used by the algorithm (Jordan–Wigner, Lemma 4.9, p.39; §5, p.43) → hypothesis ∀ i, Q.γ i = jw Q i, and the learner receives toReg of the physical Gibbs state; reason: gate counts depend on the representation; the paper's circuits use the Jordan–Wigner encoding, and jw is a CAR family (proved in the sanity file)
--   - encoding: time polynomial in n, 1/η and log(1/δ) (for fixed β) → L.time ≤ C′(N·η⁻¹·log(1/δ))^K with C′, K depending on β; reason: every polynomial in these variables is so bounded because n ≥ 1, η⁻¹ > 2 and log(1/δ) > log 2, and conversely
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Theorem 3.1, p.18 (Algorithm 3 and proof, pp.33–34)

import Mathlib
import Definitions.Def_SYKLearn_Basic
import Definitions.Def_StationarityTest_Learner

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn

/-- **Theorem 3.1 (Direction recovery)**, p.18 (Anshu–Arunachalam–Chen–Hwang, *Efficiently
Learning SYK Hamiltonians*, STOC 2027 submission, held file sha256 5d7d199a…). For every fixed
known `β > 0`, there are constants `C_β, n₀(β) > 0` such that the following holds. For every even
`n ≥ n₀(β)`, with probability at least `1 − C_β/n` over SYK couplings `g`, the following guarantee
holds for every `η, δ ∈ (0, 1/2)`. Given copies of `ρ_{β,g}`, Algorithm 3 uses at most
`C_β n^{18} max{η^{−2}, m²} log(n/δ)` independent copies and time polynomial in `n`, `1/η`, and
`log(1/δ)`, and returns a real unit vector `d̂` satisfying
`Pr_alg[‖d̂ − d‖₂ ≤ η | g] ≥ 1 − δ`, `d = g/‖g‖₂`.

**Formalization Note.** Algorithm 3 is not specified at gate level (it measures `Γ_J` and runs an
SVD "to polynomially many bits", p.33), so the statement asserts a learner in the published model
`StationarityTest.GibbsLearner` on the `N/2`-qubit register: adaptive rounds on fresh copies of the
**physical** Gibbs state `e^{−βH_g}/tr e^{−βH_g}` (`toReg (gibbs (hamiltonian Q w) β)`), gates
`{H, T, CNOT}` with Boolean classical control, computational-basis measurements, a Boolean output
circuit; `time` counts gates, ancillas and Boolean gates. The learner is chosen after
`β, N, Q, G, η, δ` and before the coupling `w`; the good set `G` is chosen before `η, δ`. Its output
bits are read by the fixed decoder `decodeBlocks` as a real vector `v`, and the returned unit
vector is `d̂ = v/‖v‖` (the event requires `v ≠ 0`). "Time polynomial in `n, 1/η, log(1/δ)`" is
`C′(n η^{−1} log(1/δ))^K` with `C′, K` depending on `β` (equivalent, since `n ≥ 1`, `η^{−1} > 2`,
`log(1/δ) > log 2`). The same `C_β` bounds the probability and the copies, as on the page. The
Majoranas are pinned to Jordan–Wigner (`Q.γ = jw Q`), the encoding the paper's circuits use, since
gate counts depend on the representation. `Q.J = 1`. -/
theorem theorem_3_1 :
    ∀ β : ℝ, 0 < β → ∃ Cβ : ℝ, ∃ n₀ : ℕ, ∃ C' : ℝ, ∃ K : ℕ, 0 < Cβ ∧ 0 < n₀ ∧ 0 < C' ∧
      ∀ (N : ℕ) (Q : Model N), n₀ ≤ N → Q.J = 1 → (∀ i, Q.γ i = jw Q i) →
        ∃ G : Set (Disorder N), disorderLaw Q Gᶜ ≤ ENNReal.ofReal (Cβ / N) ∧
          ∀ η δ : ℝ, 0 < η → η < 1 / 2 → 0 < δ → δ < 1 / 2 →
            ∃ len wp : ℕ, ∃ L : StationarityTest.GibbsLearner (N / 2) (m N * (len + 1)),
              (L.copiesUsed : ℝ) ≤
                Cβ * (N : ℝ) ^ 18 * max (η⁻¹ ^ 2) ((m N : ℝ) ^ 2) * Real.log (N / δ) ∧
              (L.time : ℝ) ≤ C' * ((N : ℝ) * η⁻¹ * Real.log (1 / δ)) ^ K ∧
              ∀ w ∈ G, 1 - δ ≤ L.successProb (toReg (gibbs (hamiltonian Q w) β))
                (fun x =>
                  StationarityTest.decodeBlocks (Fintype.equivFin (SYKEdge.KSet N 4)) len wp x ≠ 0 ∧
                  cnorm (fun I =>
                    StationarityTest.decodeBlocks (Fintype.equivFin (SYKEdge.KSet N 4)) len wp x I /
                      cnorm (StationarityTest.decodeBlocks
                        (Fintype.equivFin (SYKEdge.KSet N 4)) len wp x) -
                    w I / cnorm w) ≤ η) := by sorry

end SYKLearn
