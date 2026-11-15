-- Prove2me | Theorems.Thm_TwoOptAllExp_TSP_Supplement_lemma_25
-- name    : TwoOptAllExp.TSP.Supplement.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:52:05.453185+00:00
-- url     : https://prove2.me/theorems/0bf62102-f050-4fa3-9a17-a92f3799031f
-- title:
--   Lemma 25 — bijection between linear extensions of $D_n$ and maximal improving flip sequences from $\sigma_0$
-- statement:
--   In the instance $I_n$ ($n\ge1$) of Section 5 with $\Omega_n=(\omega_1,\dots,\omega_{T_n})$, the map
--
--   $$(s_1,\dots,s_{T_n})\longmapsto(\omega_{s_1},\dots,\omega_{s_{T_n}})$$
--
--   is a bijection between the linear extensions of $D_n$ and the maximal improving flip sequences of $I_n$ starting from the all-zero assignment $\sigma_0$: the image of every linear extension is such a sequence, every such sequence is the image of a linear extension, and distinct linear extensions have distinct images.
--
--   Differences from the source:
--   - encoding: the map is a bijection → four clauses: every labelled linear extension is (the vertex list of) a maximal improving sequence from σ₀; every maximal sequence is a labelled linear extension; any sequence equal to a labelled linear extension is maximal; the labelling is injective on linear extensions; reason: a function that is well defined into, onto and injective on the two sets
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Lemma 25, p. 34

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA232

namespace TwoOptAllExp.TSP.Supplement

open MCA232 MCA232.Vx

/-- **Lemma 25** (p. 34). The map `(s_1, …, s_{T_n}) ↦ (ω_{s_1}, …, ω_{s_{T_n}})` is a bijection between
all linear extensions of `D_n` and all maximal improving flip sequences of `I_n` starting from the
initial solution `σ₀`. -/
theorem lemma_25 (n : ℕ) (hn : 1 ≤ n) :
    (∀ s : List ℕ, IsLinExt n s →
      ∃ ys : List (V n), IsMaximalFlipSeq (inst n).Φ (σ₀ n) ys ∧
        ys.map Subtype.val = label (Omega n) s) ∧
    (∀ ys : List (V n), IsMaximalFlipSeq (inst n).Φ (σ₀ n) ys →
      ∃ s : List ℕ, IsLinExt n s ∧ ys.map Subtype.val = label (Omega n) s) ∧
    (∀ (ys : List (V n)) (s : List ℕ), IsLinExt n s →
      ys.map Subtype.val = label (Omega n) s → IsMaximalFlipSeq (inst n).Φ (σ₀ n) ys) ∧
    (∀ s s' : List ℕ, IsLinExt n s → IsLinExt n s' →
      label (Omega n) s = label (Omega n) s' → s = s') := by sorry

end TwoOptAllExp.TSP.Supplement
