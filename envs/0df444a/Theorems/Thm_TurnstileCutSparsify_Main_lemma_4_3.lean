-- Prove2me | Theorems.Thm_TurnstileCutSparsify_Main_lemma_4_3
-- name    : TurnstileCutSparsify.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:42:24.144996+00:00
-- url     : https://prove2.me/theorems/8b3df1a3-95a4-4360-a89c-1681afe535a1
-- title:
--   Lemma 4.3 — on selection success, nonedges are never selected and a positive edge is selected iff it survives to layer j_e, at layer j_e
-- statement:
--   Throughout, $G=(V,E,w)$ has integer weights $w_e\in\{0,\dots,U\}$ on $n\ge2$ vertices, $0<\varepsilon<1$, $0<\delta<1/4$, the parameters are those of (4), and the query cuts come from a rooted forest with a choice $q(e)$ of a minimum-weight path edge for each eligible pair (5) and are **accurate** (Definition 4.1).
--
--   Assume selection success (14). Then:
--   1. a nonedge ($w_e=0$) is never selected;
--   2. a positive edge $e$ is selected if and only if it survives to layer $j_e$, and in that case it is selected at layer $j_e$: $e\in E^\star\iff I_{e,j_e}=1$, and $\hat j_e=j_e$ if $e\in E^\star$;
--   3. if $\eta_e=1$ then $w_e<7t_e(k_e)/24$, that is, $w_e2^{k_e}<7t_e(0)/24$.
--
--   Here $E^\star$ is the set selected by pair enumeration, $k_e$ is the baseline layer (15) and $\eta_e$, $j_e$ are defined by the hypothetical query (16).
--
--   Differences from the source:
--   - generalization: the constants of (4) ("sufficiently large") and the selection width B (B_S from §7.1) → any positive C_B, C_R, C_β and any selection width 2^b; reason: the proof (p. 17) uses only (14), (6), integrality of w and k_e + 1 ≤ J, which hold whenever β ≥ 1; the paper's choices are instances
--   - generalization: query cuts from exact Gomory–Hu trees (§3.1) or from the query forests of Lemma 7.2, ties broken deterministically → any acyclic rooted forest F with any choice q of a minimum-weight edge on the tree path of each eligible pair (QueryChoice), accurate for w (Accurate); reason: §§4–6 use the query cuts only through accuracy (Definition 4.1) and their independence from the tables (pp. 15–16; Lemma 7.3 proof, p. 32); the paper's forests and tie-breaking are instances
--   - generalization: standing assumption M, U, δ⁻¹ ≤ n^{O(1)} (§2, p. 9) → not assumed (n ≥ 2, U ≥ 1, 0 < ε < 1, 0 < δ < 1/4 only); reason: the proofs of §§4–6 never use it (it bounds bit lengths, Appendix A); the statement covers more instances
--   - encoding: layers 0, …, J; rows, repetitions and groups in [R]; diagnostic copies i ∈ {1, 2}; Rademacher signs ±1 → layers k : ℕ with k ≤ J; rows, repetitions, groups in Fin R (0-based); copies in Fin 2; survival coins ξ_{e,a}, a ∈ Fin J; a sign is a bit (true = −1, sgnB); reason: re-indexing only
-- source:
--   Lin, Mirrokni, Woodruff (2026), Near-Optimal Space and Time Cut Sparsification in Turnstile Streams, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), Lemma 4.3, p. 17

import Mathlib
import Definitions.Def_TurnstileCutSparsify_Main_Graph
import Definitions.Def_TurnstileCutSparsify_Main_Streaming
import Definitions.Def_TurnstileCutSparsify_Main_Forest
import Definitions.Def_TurnstileCutSparsify_Main_Randomness
import Definitions.Def_TurnstileCutSparsify_Main_Sketch

open scoped BigOperators Classical
open TurnstileRank.TightBounds.RAM

namespace TurnstileCutSparsify.Main

/-- **Lemma 4.3** (Two possible layers; Lin, Mirrokni, Woodruff, arXiv:2611.03604 (version of November 3, 2026, SHA-256 7beb32bf…), p. 17).
Assume selection success (14). Then: (1) a nonedge is never selected; (2) a positive edge `e` is
selected if and only if it survives to layer `j_e`, and in that case it is selected at layer `j_e`:
`e ∈ E⋆ ⟺ I_{e,j_e} = 1` and `ĵ_e = j_e` if `e ∈ E⋆`; (3) if `η_e = 1` then `w_e < 7 t_e(k_e)/24`,
that is, `w_e 2^{k_e} < 7 t_e(0)/24`. Here the query cuts are accurate, the parameters are those of
(4) for any positive constants `C_B, C_R, C_β`, and the selection width `2^b` is arbitrary. -/
theorem lemma_4_3 (n U : ℕ) (ε δ CB CR Cβ : ℝ) (hn : 2 ≤ n) (hU : 1 ≤ U) (hε : 0 < ε)
    (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1 / 4) (hCB : 0 < CB) (hCR : 0 < CR) (hCβ : 0 < Cβ)
    (b : ℕ) (w : Pair n → ℕ) (hw : ∀ e, w e ≤ U) (F : RootedForest n) (q : Pair n → Fin n)
    (hF : F.IsAcyclic) (hq : QueryChoice F q) (hacc : Accurate (toR w) F q) :
    let P : SketchParams := ⟨n, U, ε, δ, CB, CR, Cβ⟩
    let S : Setup := ⟨⟨P, b, fun e => (w e : ℤ)⟩, F, q⟩
    ∀ (ξ : SurvBits n P.J) (sc : SelCoins n P.J P.R b), S.SelSucc ξ sc →
      (∀ e, w e = 0 → e ∉ S.selected ξ sc S.enumCands) ∧
      (∀ e, 0 < w e →
        (e ∈ S.selected ξ sc S.enumCands ↔ S.surv ξ e (S.jLay ξ sc e) = 1) ∧
        (e ∈ S.selected ξ sc S.enumCands → S.jhat ξ sc e = some (S.jLay ξ sc e))) ∧
      (∀ e, 0 < w e → S.η ξ sc e = 1 →
        S.xr e < 7 * S.t e (S.kBase e) / 24 ∧ S.xr e * 2 ^ (S.kBase e) < 7 * S.t e 0 / 24) := by sorry

end TurnstileCutSparsify.Main
