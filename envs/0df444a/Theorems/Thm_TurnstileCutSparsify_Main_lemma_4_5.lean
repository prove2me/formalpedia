-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_4_5
-- name    : TurnstileCutSparsify.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:42:18.916657+00:00
-- url     : https://prove2.me/theorems/77eb09bf-141d-4ee5-a252-63f3fd7e2e9d
-- title:
--   Lemma 4.5 — the weight error has the quadratic-sign form (17) and is unbiased; ŵ_e > w_e/2 > 0 for all selected edges except with probability δ/20
-- statement:
--   Throughout, $G=(V,E,w)$ has integer weights $w_e\in\{0,\dots,U\}$ on $n\ge2$ vertices, $0<\varepsilon<1$, $0<\delta<1/4$, the parameters are those of (4), and the query cuts come from a rooted forest with a choice $q(e)$ of a minimum-weight path edge for each eligible pair (5) and are **accurate** (Definition 4.1).
--
--   Fix any survival bits, selection seeds, estimation hashes and diagnostic signs such that (13), (14) and the conclusion of Lemma 4.4 hold. Conditional on these choices, every selected edge satisfies
--   $$\hat w_e-w_e=\frac1R\sum_{l=1}^R\sum_{f\ne e}v_e(f)\,\sigma^{j_e,r_e,l}_e\sigma^{j_e,r_e,l}_f,\qquad\mathbb E_\sigma\hat w_e=w_e.\qquad(17)$$
--   With additional failure probability at most $\delta/20$ over the evaluation signs, $\hat w_e>w_e/2>0$ for every selected edge.
--
--   Differences from the source:
--   - reading: "with the constants in (4)": sufficiently large absolute constants C_B and C_R, and then C_β (p. 12) → ∃ CB₀ CR₀, ∀ CB ≥ CB₀, ∀ CR ≥ CR₀, ∃ Cβ₀, ∀ Cβ ≥ Cβ₀, stated before n, U, ε, δ, w and the forest; reason: the order of choice on p. 12; the constants never depend on n, U, ε, δ or the input
--   - generalization: query cuts from exact Gomory–Hu trees (§3.1) or from the query forests of Lemma 7.2, ties broken deterministically → any acyclic rooted forest F with any choice q of a minimum-weight edge on the tree path of each eligible pair (QueryChoice), accurate for w (Accurate); reason: §§4–6 use the query cuts only through accuracy (Definition 4.1) and their independence from the tables (pp. 15–16; Lemma 7.3 proof, p. 32); the paper's forests and tie-breaking are instances
--   - generalization: standing assumption M, U, δ⁻¹ ≤ n^{O(1)} (§2, p. 9) → not assumed (n ≥ 2, U ≥ 1, 0 < ε < 1, 0 < δ < 1/4 only); reason: the proofs of §§4–6 never use it (it bounds bit lengths, Appendix A); the statement covers more instances
--   - encoding: (17) for every selected edge (at layer ĵ_e = j_e, row r_e); E_σ ŵ_e; "ŵ_e > w_e/2 > 0" → for e ∈ E⋆ and k, r with jhat = some k, row = some r: the identity for every σ (sum over f ∈ univ.erase e, signs at layer j_e) and expect over uniform σ; 0 < w_e/2 for every selected e (deterministic) and the probability bound for ŵ_e > w_e/2; reason: ŵ_e is computed at (ĵ_e, r_e); the positivity of w_e/2 involves no evaluation sign
--   - encoding: "failure probability over X" with the other randomness fixed → prob over the uniform distribution of the seeds of X (survival bits: all of Pair n → Fin J → Bool; evaluation signs: all sign assignments), every other random choice a fixed argument; reason: fully independent bits and independently seeded families are product uniform distributions on finite sets
--   - reading: groups P_1, …, P_R "a fixed partition" of the 32R difference queries; r_e = arg min ψ_r(e) with ties "broken deterministically"; medians of R values → P_g = {32g, …, 32g + 31}; r_e the first row minimizing ψ_r(e) (List.argmin); median = middle entry (index ⌊R/2⌋) of the sorted list; reason: the paper fixes some deterministic rule; this is one, and R is odd
--   - encoding: layers 0, …, J; rows, repetitions and groups in [R]; diagnostic copies i ∈ {1, 2}; Rademacher signs ±1 → layers k : ℕ with k ≤ J; rows, repetitions, groups in Fin R (0-based); copies in Fin 2; survival coins ξ_{e,a}, a ∈ Fin J; a sign is a bit (true = −1, sgnB); reason: re-indexing only
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 4.5, p. 19

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Forest
import Definitions.Def_TurnstileCutSparsify_Main_Randomness
import Definitions.Def_TurnstileCutSparsify_Main_Sketch

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Lemma 4.5** (Weight estimation; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 19).
Fix accurate query cuts, and fix any survival bits, selection seeds, estimation hashes and
diagnostic signs such that (13), (14) and the conclusion of Lemma 4.4 hold. Conditional on these
choices, every selected edge `e` (selected at layer `ĵ_e`, row `r_e`) satisfies (17):
`ŵ_e − w_e = (1/R) Σ_{l=1}^{R} Σ_{f ≠ e} v_e(f) σ^{j_e,r_e,l}_e σ^{j_e,r_e,l}_f` and
`E_σ ŵ_e = w_e`. With additional failure probability at most `δ/20` over the evaluation signs,
`ŵ_e > w_e/2 > 0` for every selected edge. The parameters are those of (4), for sufficiently large
absolute constants `C_B, C_R` and then `C_β`. -/
theorem lemma_4_5 :
    ∃ CB₀ CR₀ : ℝ, ∀ CB : ℝ, CB₀ ≤ CB → ∀ CR : ℝ, CR₀ ≤ CR → ∃ Cβ₀ : ℝ, ∀ Cβ : ℝ, Cβ₀ ≤ Cβ →
    ∀ (n U : ℕ) (ε δ : ℝ), 2 ≤ n → 1 ≤ U → 0 < ε → ε < 1 → 0 < δ → δ < 1 / 4 →
    ∀ (w : Pair n → ℕ), (∀ e, w e ≤ U) →
    ∀ (F : RootedForest n) (q : Pair n → Fin n), F.IsAcyclic → QueryChoice F q →
      Accurate (toR w) F q →
    let P : SketchParams := ⟨n, U, ε, δ, CB, CR, Cβ⟩
    let S : Setup := ⟨⟨P, P.bB, fun e => (w e : ℤ)⟩, F, q⟩
    ∀ (ξ : SurvBits n P.J) (sc : SelCoins n P.J P.R P.bB) (dc : DiagCoins n P.J P.R P.bB),
      S.LoadOK ξ → S.SelSucc ξ sc → S.DiagOK ξ sc dc →
      (∀ e ∈ S.selected ξ sc S.enumCands, ∀ (k : ℕ) (r : Fin P.R), S.jhat ξ sc e = some k →
          S.row ξ dc e k = some r →
        (∀ σ : EvalSigns n P.J P.R, S.what ξ dc σ e k r - S.xr e =
          (1 / (P.R : ℝ)) * ∑ l : Fin P.R, ∑ f ∈ Finset.univ.erase e,
            S.coll ξ dc e (S.jLay ξ sc e) r f *
              (sgnB (σ (S.lay (S.jLay ξ sc e)) r l e) : ℝ) *
              (sgnB (σ (S.lay (S.jLay ξ sc e)) r l f) : ℝ)) ∧
        expect (fun σ : EvalSigns n P.J P.R => S.what ξ dc σ e k r) = S.xr e) ∧
      (∀ e ∈ S.selected ξ sc S.enumCands, 0 < S.xr e / 2) ∧
      prob (fun σ : EvalSigns n P.J P.R => ¬ ∀ e ∈ S.selected ξ sc S.enumCands,
        ∀ (k : ℕ) (r : Fin P.R), S.jhat ξ sc e = some k → S.row ξ dc e k = some r →
          S.xr e / 2 < S.what ξ dc σ e k r) ≤ δ / 20 := by sorry

end TurnstileCutSparsify.Main
