-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_proposition_6_2
-- name    : TurnstileCutSparsify.Main.proposition_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:42:28.946926+00:00
-- url     : https://prove2.me/theorems/a39b62f6-536b-419d-bb03-3559dd06a266
-- title:
--   Proposition 6.2 — correctness of the decoder (pair enumeration) for fixed accurate query cuts, outside eight events of probability ≤ δ/20 each
-- statement:
--   Throughout, $G=(V,E,w)$ has integer weights $w_e\in\{0,\dots,U\}$ on $n\ge2$ vertices, $0<\varepsilon<1$, $0<\delta<1/4$, the parameters are those of (4), and the query cuts come from a rooted forest with a choice $q(e)$ of a minimum-weight path edge for each eligible pair (5) and are **accurate** (Definition 4.1).
--
--   Fix accurate query cuts independent of the three tables, and let the survival bits and evaluation signs be fully independent. Outside eight events, each of probability at most $\delta/20$, the decoder of Section 3.3 returns a positive reweighting $H$ of a set $E^\star\subseteq E$ of at most $8n\beta=O(n\varepsilon^{-2}\log^2n)$ edges, and $H$ is a $(1\pm\varepsilon)$-cut sparsifier of $G$.
--
--   Differences from the source:
--   - reading: "with the constants in (4)": sufficiently large absolute constants C_B and C_R, and then C_β (p. 12) → ∃ CB₀ CR₀, ∀ CB ≥ CB₀, ∀ CR ≥ CR₀, ∃ Cβ₀, ∀ Cβ ≥ Cβ₀, stated before n, U, ε, δ, w and the forest; reason: the order of choice on p. 12; the constants never depend on n, U, ε, δ or the input
--   - generalization: query cuts from exact Gomory–Hu trees (§3.1) or from the query forests of Lemma 7.2, ties broken deterministically → any acyclic rooted forest F with any choice q of a minimum-weight edge on the tree path of each eligible pair (QueryChoice), accurate for w (Accurate); reason: §§4–6 use the query cuts only through accuracy (Definition 4.1) and their independence from the tables (pp. 15–16; Lemma 7.3 proof, p. 32); the paper's forests and tie-breaking are instances
--   - generalization: selection hashes and signs, estimation hashes and diagnostic signs: uniform random cubic polynomials over F_(2^m) (App. A.4), four-wise independent with independent seeds → selection hashes and signs, estimation hashes and diagnostic signs drawn from arbitrary seeded families that are four-wise independent with uniform marginals (KWiseUniform 4), one independent uniform seed per function; reason: the proofs use only four-wise independence (pp. 16, 18, 27); the Appendix A.4 families are instances
--   - generalization: standing assumption M, U, δ⁻¹ ≤ n^{O(1)} (§2, p. 9) → not assumed (n ≥ 2, U ≥ 1, 0 < ε < 1, 0 < δ < 1/4 only); reason: the proofs of §§4–6 never use it (it bounds bit lengths, Appendix A); the statement covers more instances
--   - encoding: outside eight events, each of probability at most δ/20, the decoder returns a positive reweighting H of E⋆ ⊆ E of at most 8nβ = O(nε⁻² log² n) edges → ∃ E : Fin 8 → (TableRand … → Prop) with prob (E i) ≤ δ/20 and, whenever no E i holds, decode … enumCands = some H with support(H) = E⋆, IsPosReweighting w H, |E⋆| ≤ 8nβ, IsCutSparsifier ε w H; reason: "= O(nε⁻² log² n)" is the estimate β = O(ε⁻² log² n) of p. 12, not a separate claim; the bound 8nβ is kept explicit
--   - encoding: "failure probability over X" with the other randomness fixed → prob over the uniform distribution of the seeds of X (survival bits: all of Pair n → Fin J → Bool; evaluation signs: all sign assignments), every other random choice a fixed argument; reason: fully independent bits and independently seeded families are product uniform distributions on finite sets
--   - reading: groups P_1, …, P_R "a fixed partition" of the 32R difference queries; r_e = arg min ψ_r(e) with ties "broken deterministically"; medians of R values → P_g = {32g, …, 32g + 31}; r_e the first row minimizing ψ_r(e) (List.argmin); median = middle entry (index ⌊R/2⌋) of the sorted list; reason: the paper fixes some deterministic rule; this is one, and R is odd
--   - encoding: layers 0, …, J; rows, repetitions and groups in [R]; diagnostic copies i ∈ {1, 2}; Rademacher signs ±1 → layers k : ℕ with k ≤ J; rows, repetitions, groups in Fin R (0-based); copies in Fin 2; survival coins ξ_{e,a}, a ∈ Fin J; a sign is a bit (true = −1, sgnB); reason: re-indexing only
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Proposition 6.2, p. 25

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Forest
import Definitions.Def_TurnstileCutSparsify_Main_Randomness
import Definitions.Def_TurnstileCutSparsify_Main_Sketch

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Proposition 6.2** (Correctness for accurate query cuts; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 25).
Fix accurate query cuts independent of the three tables, and let the survival bits and evaluation
signs be fully independent (the hashes, selection signs and diagnostic signs come from any
four-wise independent families with independent seeds). Outside eight events, each of probability
at most `δ/20`, the decoder of Section 3.3 (pair enumeration) returns a positive reweighting `H` of
a set `E⋆ ⊆ E` of at most `8nβ = O(nε⁻² log² n)` edges, and `H` is a `(1 ± ε)`-cut sparsifier of
`G`. The parameters are those of (4), for sufficiently large absolute constants `C_B, C_R` and then
`C_β`. -/
theorem proposition_6_2 :
    ∃ CB₀ CR₀ : ℝ, ∀ CB : ℝ, CB₀ ≤ CB → ∀ CR : ℝ, CR₀ ≤ CR → ∃ Cβ₀ : ℝ, ∀ Cβ : ℝ, Cβ₀ ≤ Cβ →
    ∀ (n U : ℕ) (ε δ : ℝ), 2 ≤ n → 1 ≤ U → 0 < ε → ε < 1 → 0 < δ → δ < 1 / 4 →
    ∀ (w : Pair n → ℕ), (∀ e, w e ≤ U) →
    ∀ (F : RootedForest n) (q : Pair n → Fin n), F.IsAcyclic → QueryChoice F q →
      Accurate (toR w) F q →
    let P : SketchParams := ⟨n, U, ε, δ, CB, CR, Cβ⟩
    let S : Setup := ⟨⟨P, P.bB, fun e => (w e : ℤ)⟩, F, q⟩
    ∀ {HS SS TS DS : Type} [Fintype HS] [Fintype SS] [Fintype TS] [Fintype DS]
      (FH : HS → Pair n → Fin (2 ^ P.bB)) (FS : SS → Pair n → Bool)
      (FT : TS → Pair n → Fin (2 ^ P.bB)) (FD : DS → Pair n → Bool),
      KWiseUniform 4 FH → KWiseUniform 4 FS → KWiseUniform 4 FT → KWiseUniform 4 FD →
      ∃ E : Fin 8 → TableRand n P.J P.R HS SS TS DS → Prop,
        (∀ i, prob (E i) ≤ δ / 20) ∧
        ∀ ω, (∀ i, ¬ E i ω) →
          ∃ H : Pair n → ℝ,
            S.decode ω.1 (SelCoins.ofSeeds FH FS ω.2.1) (DiagCoins.ofSeeds FT FD ω.2.2.1) ω.2.2.2
              S.enumCands = some H ∧
            Finset.univ.filter (fun e => H e ≠ 0) =
              S.selected ω.1 (SelCoins.ofSeeds FH FS ω.2.1) S.enumCands ∧
            IsPosReweighting (toR w) H ∧
            (S.selected ω.1 (SelCoins.ofSeeds FH FS ω.2.1) S.enumCands).card ≤ 8 * n * P.β ∧
            IsCutSparsifier ε (toR w) H := by sorry

end TurnstileCutSparsify.Main
