-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_24
-- name    : TwoOptAllExp.TSP.Supplement.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:51:15.505885+00:00
-- url     : https://prove2.me/theorems/b2128580-7bf3-4ef7-8cc4-9fd795bd8e29
-- title:
--   Lemma 24 — restricted maximal runs of a recursive block are the labelled linear extensions of $D_m$
-- statement:
--   In the instance $I_n$ ($n\ge1$) of Section 5 fix $0\le m\le n$ and $\varepsilon\in\{0,1\}$, and let $\sigma$ be an assignment such that
--
--   1. $F_0,\dots,F_m$ are in phase $\varepsilon$;
--   2. among the variables of $F_0\cup\dots\cup F_m$, exactly $v_{m,1}$ is improving;
--   3. if $m\ge1$, the external neighbor of $v_{m,8}$ ($u_{m+1,0}$ if $m\ne n$, $v'_0$ if $m=n$) has value $\varepsilon$;
--
--   and let all neighbors of these layers outside them stay fixed (only variables of $F_0,\dots,F_m$ are flipped). Then the maximal improving flip sequences restricted to $F_0,\dots,F_m$ are exactly the strings $(\xi_{s_1},\dots,\xi_{s_{T_m}})$ obtained by labeling the linear extensions $(s_1,\dots,s_{T_m})$ of $D_m$ with the entries of $\Xi_m^\varepsilon$; moreover $|\Xi_m^\varepsilon|=T_m$, and after any such sequence (of $T_m$ flips) the layers $F_0,\dots,F_m$ are in phase $1-\varepsilon$.
--
--   Differences from the source:
--   - reading: values of all neighbors of F_0 ∪ ⋯ ∪ F_m outside these layers remain fixed until v_{m,8} flips (and the external neighbor of v_{m,8} remains fixed); maximal improving flip sequences restricted to F_0, …, F_m → sequences that flip only variables of these layers (all other variables keep their values throughout), each flip improving, ending when no variable of these layers is improving; reason: restriction to these layers freezes the exterior; before the terminal flip of v_{m,8}, interspersed exterior moves allowed by the source can change no neighbor and hence no internal gain. The source proof on p. 34 ends the block at that flip, with no further improving vertex in the block
--   - encoding: among the variables in these layers only v_{m,1} is improving → for every vertex x of the layers: x improving ↔ x = v_{m,1}; reason: includes that v_{m,1} is improving
--   - encoding: strings obtained by labeling linear extensions of D_m with Ξ_m^ε → ys.map val = label (Xi ε m) s for a linear extension s; reason: 1-based positions
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 24, p. 33 (proof pp. 33–34)

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232

namespace TwoOptAllExp.TSP.Supplement

open MCA232 MCA232.Vx

/-- **Lemma 24** (p. 33). Fix `0 ≤ m ≤ n` and `ε ∈ {0, 1}`. Suppose `F_0, …, F_m` are in phase `ε`,
and among the variables in these layers only `v_{m,1}` is improving. Suppose the values of all
neighbors of `F_0 ∪ ⋯ ∪ F_m` outside these layers stay fixed (only variables of these layers flip),
and, if `m ≥ 1`, that the external neighbor of `v_{m,8}` (`u_{m+1,0}` if `m ≠ n`, `v′_0` if `m = n`) has
value `ε`. Then the maximal improving flip sequences restricted to `F_0, …, F_m` are exactly the
strings obtained by labeling the linear extensions of `D_m` with the entries of `Ξ_m^ε`; after all
`|Ξ_m^ε| = T_m` flips the layers `F_0, …, F_m` are in phase `1 - ε`. -/
theorem lemma_24 (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : m ≤ n) (ε : Bool) (σ : V n → Bool)
    (hphase : InPhase σ m ε)
    (himp : ∀ x : V n, x.1 ∈ lowLayers m → (Improving σ x ↔ x.1 = v m 1))
    (hext : 1 ≤ m → val σ (if m < n then u0 (m + 1) else vp 0) = ε) :
    (∀ ys : List (V n), IsMaxRestricted (lowLayers m) σ ys ↔
      ∃ s : List ℕ, IsLinExt m s ∧ ys.map Subtype.val = label (Xi ε m) s) ∧
    (Xi ε m).length = T m ∧
    ∀ ys : List (V n), IsMaxRestricted (lowLayers m) σ ys →
      ys.length = T m ∧ InPhase (applyFlips σ ys) m (!ε) := by sorry

end TwoOptAllExp.TSP.Supplement
