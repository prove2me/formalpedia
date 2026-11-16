-- Prove2me | Theorems.Thm_SYKLearn_Supplement_theorem_1_2
-- name    : SYKLearn.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:37:21.24044+00:00
-- url     : https://prove2.me/theorems/cb9c3172-7c98-4ba5-968b-9e886de03dcf
-- title:
--   Theorem 1.2 — SYK direction to error $\varepsilon$ up to sign from $Cn^{44}\delta^{-4}\varepsilon^{-2}\log(n/\zeta)$ applications of $U_\star=e^{-\iota t_\star H_g}$ at one fixed time $t_\star\ge1$
-- statement:
--   Let $H_g=\sum_{|I|=4}g_I\Gamma_I$ be the SYK Hamiltonian on $n$ Majorana modes (Jordan–Wigner operators on $n/2$ qubits), with $g_I\sim\mathcal N(0,\sigma_n^2)$ i.i.d., $\sigma_n^2=6/n^3$, and write $d=g/\|g\|_2$.
--
--   There are universal constants $c,C>0$, $N_0$, and a universal polynomial bound $C'(\cdot)^K$, such that the following holds. For every even $n\ge N_0$, every deterministic time $t_\star\ge1$, and all $0<\varepsilon\le1$, $0<\delta,\zeta\le1/2$, there is a set $G$ of coupling vectors with
--   $$\Pr_g[g\notin G]\le\delta+Ce^{-cn},$$
--   and there is one quantum algorithm with oracle access to the unitary $U_\star=e^{-\iota t_\star H_g}$ such that
--
--   1. it makes at most $Cn^{44}\delta^{-4}\varepsilon^{-2}\log(n/\zeta)$ applications of $U_\star$, so its total evolution time is at most $Cn^{44}\delta^{-4}\varepsilon^{-2}\log(n/\zeta)\cdot t_\star$;
--   2. its gate and classical processing cost, excluding the calls to $U_\star$, is at most $C'\,(n\,\delta^{-1}\varepsilon^{-1}\log(1/\zeta))^K$;
--   3. for every $g\in G$, with probability at least $1-\zeta$ it outputs a unit vector $\hat d$ with
--   $$\min_{s\in\{-1,1\}}\|\hat d-s\,d\|_2\le\varepsilon .$$
--
--   This is the dynamical counterpart of the Gibbs-state learning theorem: access to time evolution at a single fixed time suffices to learn the direction of the couplings, up to the unavoidable sign.
--
--   **Formalization Note** The algorithm is an `EvolutionLearner` on the $n/2$-qubit register, fixed before the coupling; its oracle is the exact matrix exponential $e^{-\iota t_\star H_g}$ transported to the learner's wires, applied forward and without coherent control. Its output bits are read as a real vector $v$ by the fixed dyadic decoder, and $\hat d=v/\|v\|_2$ with $v\neq0$ required.
--
--   Differences from the source:
--   - encoding: Gaussian couplings g_I i.i.d. N(0, σ_n²), σ_n² = 6/n³ → disorderLaw Q (product of N(0, 6J²/N³)) with the hypothesis Q.J = 1; reason: with J = 1 the law is exactly the paper's; n even and n ≥ 4 come from Model
--   - encoding: with probability at least 1 − δ − Ce^{−cn} over g → a set G whose complement has (outer) measure at most δ + Ce^{−cn}; reason: equivalent for measurable events, and no measurability of the event is assumed
--   - encoding: Pauli strings and qubit product states in the Jordan–Wigner encoding (§5, p.43) → hypothesis ∀ i, Q.γ i = jw Q i, and the oracle is toReg of the matrix exponential on the learner's N/2 wires; reason: gate counts depend on the representation; the paper's circuits use the Jordan–Wigner encoding
--   - reading: “there exists an algorithm making N applications of the unitary U⋆ … The gate and classical processing costs, excluding the calls to U⋆” (no model of computation named) → an EvolutionLearner (the published GibbsLearner model with oracle calls to the unknown unitary in place of copies: {H, T, CNOT} gates with Boolean classical control, computational-basis measurement, Boolean output circuit; time = gates + ancillas + Boolean gates, oracle calls excluded; oracle applied forward and uncontrolled); its output bits are decoded by decodeBlocks into v and d̂ = v/‖v‖₂ (v ≠ 0 required); reason: the paper names no model; this is the platform's learner model, in which the paper's Pauli-eigenstate preparations and Pauli measurements (§5.2) and the classical SVD run
--   - reading: “with probability at least 1 − δ − Ce^{−cn} over Gaussian couplings g, there exists an algorithm” → one set G of couplings, then one learner fixed before the coupling w ∈ G; reason: a learner chosen after the coupling could output g/‖g‖₂ with no calls, which empties the theorem; the proof's algorithm depends only on n, ε, δ, ζ
--   - reading: making N = Cn^{44}δ^{−4}ε^{−2} log(n/ζ) applications → L.queriesUsed ≤ C·N^44·δ^{−4}·ε^{−2}·log(N/ζ), with the same C as in the probability bound; reason: N is not an integer in general, so it is an upper bound on the number of calls (the proof makes m²R ≤ N calls)
--   - encoding: gate and classical costs polynomial in n, δ⁻¹, ε⁻¹ and log(1/ζ) → L.time ≤ C′·(N·δ⁻¹·ε⁻¹·log(1/ζ))^K with universal C′ > 0 and K; reason: every polynomial in these variables is so bounded since n ≥ 1, δ⁻¹ ≥ 2, ε⁻¹ ≥ 1 and log(1/ζ) ≥ log 2, and conversely
--   - encoding: the total evolution time is Nt⋆ → L.queriesUsed · t⋆ ≤ C·N^44·δ^{−4}·ε^{−2}·log(N/ζ)·t⋆; reason: each call evolves for time t⋆, so this restates the query bound
--   - encoding: universal constant N_0 > 0 (real) → N₀ : ℕ with N₀ ≤ N; reason: a real threshold can be replaced by its ceiling, and n ≥ 4 > 0 holds in Model
--   - encoding: min over s ∈ {−1, 1} of ‖d̂ − sd‖₂ ≤ ε → ‖d̂ − d‖₂ ≤ ε ∨ ‖d̂ + d‖₂ ≤ ε; reason: the minimum over two values
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Theorem 1.2, p.3 (restated p.43; proof §5, pp.43–45)

import Mathlib
import Definitions.Def_SYKLearn_Basic
import Definitions.Def_SYKLearn_Supplement_EvolutionLearner

noncomputable section
open MeasureTheory SYKFastMix.FastMixing

namespace SYKLearn.Supplement

/-- **Theorem 1.2 (Efficient learning of SYK Hamiltonians from long time evolution)**, p.3
(restated p.43) (Anshu–Arunachalam–Chen–Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission, held file sha256 5d7d199a…). There are universal constants `c, C, N₀ > 0` such that
the following holds. For every even `n ≥ N₀`, every deterministic `t⋆ ≥ 1`, and `0 < ε ≤ 1`,
`0 < δ, ζ ≤ 1/2`, with probability at least `1 − δ − Ce^{−cn}` over Gaussian couplings `g`, there
exists an algorithm making `N = Cn^{44}δ^{−4}ε^{−2} log(n/ζ)` applications of the unitary
`U⋆ = e^{−ιt⋆H_g}` and with probability at least `1 − ζ`, outputs a unit vector `d̂` satisfying
`min_{s∈{−1,1}} ‖d̂ − sd‖₂ ≤ ε`, `d = g/‖g‖₂`. The gate and classical processing costs, excluding
the calls to `U⋆`, are polynomial in `n, δ^{−1}, ε^{−1}` and `log(1/ζ)`. The total evolution time
is `Nt⋆`.

**Formalization Note.**
* The SYK model is the published `SYKFastMix.FastMixing.Model` with `Q.J = 1` (couplings
  `g_I ~ N(0, 6/n³)` i.i.d., `n` even and `n ≥ 4` built in); `N` here is the number `n` of Majorana
  modes. The Majoranas are pinned to Jordan–Wigner (`Q.γ = jw Q`): §5 (p.43) prepares qubit product
  states and measures Pauli strings in the Jordan–Wigner encoding, and gate counts depend on the
  representation.
* The oracle is the exact unitary `U⋆ = e^{−ι t⋆ H_g}` (matrix exponential `mexp`) of
  `H_g = hamiltonian Q w`, transported by `toReg` to the learner's `n/2` wires; the learner
  (`EvolutionLearner`) applies it only forward, uncontrolled, at the fixed time `t⋆`.
* Quantifiers as printed: `c, C, N₀` and the cost polynomial `C′(·)^K` are universal (independent
  of `t⋆, ε, δ, ζ`); then `n, t⋆, ε, δ, ζ`; then the set `G` of good couplings, of outer measure of
  the complement `≤ δ + Ce^{−cn}`; then ONE learner, fixed before the coupling `w ∈ G`.
* "Making `N` applications" is read as at most `N` oracle calls, with the same `C` as in the
  probability bound. "Polynomial in `n, δ^{−1}, ε^{−1}, log(1/ζ)`" is
  `≤ C′(n δ^{−1} ε^{−1} log(1/ζ))^K` (equivalent, since `n ≥ 1`, `δ^{−1} ≥ 2`, `ε^{−1} ≥ 1`,
  `log(1/ζ) ≥ log 2`). The total evolution time (calls × `t⋆`) is stated as the third clause.
* The output bits are read by `decodeBlocks` as a vector `v` of dyadic numbers indexed by the
  4-sets; the reported unit vector is `d̂ = v/‖v‖₂`, required to exist (`v ≠ 0`). The sign of `d`
  is not demanded (`min` over `s ∈ {−1, 1}` is the disjunction). -/
theorem theorem_1_2 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∃ C' : ℝ, 0 < C' ∧ ∃ K : ℕ,
      ∀ (N : ℕ) (Q : Model N), N₀ ≤ N → Q.J = 1 → (∀ i, Q.γ i = jw Q i) →
      ∀ tstar : ℝ, 1 ≤ tstar →
      ∀ ε δ ζ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ ≤ 1 / 2 → 0 < ζ → ζ ≤ 1 / 2 →
        ∃ G : Set (Disorder N),
          disorderLaw Q Gᶜ ≤ ENNReal.ofReal (δ + C * Real.exp (-(c * N))) ∧
          ∃ len wp : ℕ, ∃ L : EvolutionLearner (N / 2) (m N * (len + 1)),
            (L.queriesUsed : ℝ) ≤
              C * (N : ℝ) ^ 44 * δ ^ (-4 : ℤ) * ε ^ (-2 : ℤ) * Real.log (N / ζ) ∧
            (L.time : ℝ) ≤ C' * ((N : ℝ) * δ⁻¹ * ε⁻¹ * Real.log (1 / ζ)) ^ K ∧
            (L.queriesUsed : ℝ) * tstar ≤
              C * (N : ℝ) ^ 44 * δ ^ (-4 : ℤ) * ε ^ (-2 : ℤ) * Real.log (N / ζ) * tstar ∧
            ∀ w ∈ G, 1 - ζ ≤
              L.successProb (toReg (mexp ((-((tstar : ℂ) * Complex.I)) • hamiltonian Q w)))
                (fun x =>
                  let v := StationarityTest.decodeBlocks (Fintype.equivFin (SYKEdge.KSet N 4))
                    len wp x
                  v ≠ 0 ∧
                    (cnorm ((cnorm v)⁻¹ • v - (cnorm w)⁻¹ • w) ≤ ε ∨
                      cnorm ((cnorm v)⁻¹ • v + (cnorm w)⁻¹ • w) ≤ ε)) := by sorry

end SYKLearn.Supplement
