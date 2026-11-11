-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_4_2
-- name    : TurnstileCutSparsify.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:42:27.099334+00:00
-- url     : https://prove2.me/theorems/6265d67f-45c1-432b-a3f4-951982de21f5
-- title:
--   Lemma 4.2 — load bound (13) over the survival bits, then uniform selection accuracy (14) over the selection seeds, each failing with probability ≤ δ/20
-- statement:
--   Throughout, $G=(V,E,w)$ has integer weights $w_e\in\{0,\dots,U\}$ on $n\ge2$ vertices, $0<\varepsilon<1$, $0<\delta<1/4$, the parameters are those of (4), and the query cuts come from a rooted forest with a choice $q(e)$ of a minimum-weight path edge for each eligible pair (5) and are **accurate** (Definition 4.1).
--
--   With failure probability at most $\delta/20$ over the survival bits,
--   $$\sum_{f\in E(S_e,V\setminus S_e)}\min\{w_f/t_e(k),1\}\,I_{f,k}\le2.5\beta\qquad(13)$$
--   for every eligible pair $e$ and every layer $k$. Fix any survival bits satisfying this bound. Then, with additional failure probability at most $\delta/20$ over the selection seeds (selection hashes into $B$ buckets and selection signs),
--   $$|y_e(k)-w_eI_{e,k}|\le t_e(k)/24\qquad(14)$$
--   for every eligible pair and layer, including zero coordinates.
--
--   Differences from the source:
--   - reading: "with the constants in (4)": sufficiently large absolute constants C_B and C_R, and then C_β (p. 12) → ∃ CB₀ CR₀, ∀ CB ≥ CB₀, ∀ CR ≥ CR₀, ∃ Cβ₀, ∀ Cβ ≥ Cβ₀, stated before n, U, ε, δ, w and the forest; reason: the order of choice on p. 12; the constants never depend on n, U, ε, δ or the input
--   - generalization: query cuts from exact Gomory–Hu trees (§3.1) or from the query forests of Lemma 7.2, ties broken deterministically → any acyclic rooted forest F with any choice q of a minimum-weight edge on the tree path of each eligible pair (QueryChoice), accurate for w (Accurate); reason: §§4–6 use the query cuts only through accuracy (Definition 4.1) and their independence from the tables (pp. 15–16; Lemma 7.3 proof, p. 32); the paper's forests and tie-breaking are instances
--   - generalization: selection hashes and selection signs: uniform random cubic polynomials over F_(2^m) (App. A.4), four-wise independent with independent seeds → selection hashes and selection signs drawn from arbitrary seeded families that are four-wise independent with uniform marginals (KWiseUniform 4), one independent uniform seed per function; reason: the proofs use only four-wise independence (pp. 16, 18, 27); the Appendix A.4 families are instances
--   - generalization: standing assumption M, U, δ⁻¹ ≤ n^{O(1)} (§2, p. 9) → not assumed (n ≥ 2, U ≥ 1, 0 < ε < 1, 0 < δ < 1/4 only); reason: the proofs of §§4–6 never use it (it bounds bit lengths, Appendix A); the statement covers more instances
--   - encoding: "failure probability over X" with the other randomness fixed → prob over the uniform distribution of the seeds of X (survival bits: all of Pair n → Fin J → Bool; evaluation signs: all sign assignments), every other random choice a fixed argument; reason: fully independent bits and independently seeded families are product uniform distributions on finite sets
--   - encoding: layers 0, …, J; rows, repetitions and groups in [R]; diagnostic copies i ∈ {1, 2}; Rademacher signs ±1 → layers k : ℕ with k ≤ J; rows, repetitions, groups in Fin R (0-based); copies in Fin 2; survival coins ξ_{e,a}, a ∈ Fin J; a sign is a bit (true = −1, sgnB); reason: re-indexing only
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 4.2, p. 16

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Forest
import Definitions.Def_TurnstileCutSparsify_Main_Randomness
import Definitions.Def_TurnstileCutSparsify_Main_Sketch

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Lemma 4.2** (Load and point queries; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 16).
For accurate query cuts, with failure probability at most `δ/20` over the survival bits, the load
bound (13) `Σ_{f ∈ E(S_e, V \ S_e)} min {w_f / t_e(k), 1} I_{f,k} ≤ 2.5 β` holds for every
eligible pair `e` and every layer `k`. Fix any survival bits satisfying this bound. Then, with
additional failure probability at most `δ/20` over the selection seeds, `|y_e(k) − w_e I_{e,k}| ≤
t_e(k)/24` (14) for every eligible pair and layer, including zero coordinates. The parameters are
those of (4), for sufficiently large absolute constants `C_B, C_R` and then `C_β`; the selection
hashes and signs come from any four-wise independent families with independent seeds. -/
theorem lemma_4_2 :
    ∃ CB₀ CR₀ : ℝ, ∀ CB : ℝ, CB₀ ≤ CB → ∀ CR : ℝ, CR₀ ≤ CR → ∃ Cβ₀ : ℝ, ∀ Cβ : ℝ, Cβ₀ ≤ Cβ →
    ∀ (n U : ℕ) (ε δ : ℝ), 2 ≤ n → 1 ≤ U → 0 < ε → ε < 1 → 0 < δ → δ < 1 / 4 →
    ∀ (w : Pair n → ℕ), (∀ e, w e ≤ U) →
    ∀ (F : RootedForest n) (q : Pair n → Fin n), F.IsAcyclic → QueryChoice F q →
      Accurate (toR w) F q →
    let P : SketchParams := ⟨n, U, ε, δ, CB, CR, Cβ⟩
    let S : Setup := ⟨⟨P, P.bB, fun e => (w e : ℤ)⟩, F, q⟩
    ∀ {HS SS : Type} [Fintype HS] [Fintype SS] (FH : HS → Pair n → Fin (2 ^ P.bB))
      (FS : SS → Pair n → Bool), KWiseUniform 4 FH → KWiseUniform 4 FS →
      prob (fun ξ : SurvBits n P.J => ¬ S.LoadOK ξ) ≤ δ / 20 ∧
      ∀ ξ : SurvBits n P.J, S.LoadOK ξ →
        prob (fun s : (Fin (P.J + 1) → Fin P.R → HS) × (Fin (P.J + 1) → Fin P.R → SS) =>
          ¬ S.SelSucc ξ (SelCoins.ofSeeds FH FS s)) ≤ δ / 20 := by sorry

end TurnstileCutSparsify.Main
