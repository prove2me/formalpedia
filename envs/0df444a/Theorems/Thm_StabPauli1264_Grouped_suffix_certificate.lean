-- Prove2me | Theorems.Thm_StabPauli1264_Grouped_suffix_certificate
-- name    : StabPauli1264.Grouped.suffix_certificate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:26:43.458199+00:00
-- url     : https://prove2.me/theorems/d484585d-9ed3-48dd-b6d4-d22b53dc31d9
-- title:
--   Lemma 8.1 — Suffix certificate
-- statement:
--   Run Algorithm 1 with a nonempty window $M$, a real evaluation law $p$, and $0<\varepsilon<1$. Let $\tau=\varepsilon/2$, $k$ be the number of selected contexts, and $R_j,w_j$ the remaining indices and maximum commuting mass, including the stopping step $j=k+1$. For every commuting $T$ and $1\le j\le k+1$,
--
--   $$p(T\cap R_j)\le w_j.$$
--
--   Consequently $w_1\ge\cdots\ge w_k\ge\tau$, $k\le\lfloor1/\tau\rfloor=\lfloor2/\varepsilon\rfloor$, the terminal maximum is strictly below $\tau$, and $p(T\cap R_{k+1})<\tau$ for every commuting $T$. The objects are computed by the exact maximum-weight peeling rule, rather than supplied with a certificate hypothesis. This is the source certificate for controlling retained and discarded commuting support.
--
--   Differences from the source:
--   - encoding: source indices j=1,...,k+1 → zero-based j=0,...,k; reason: reasoning and all terminal cases are preserved by shifting indices
--   - encoding: ties broken arbitrarily in Algorithm 1 → one fixed deterministic classical choice among exact maximizers; reason: the source proof holds for every tie choice independent of the unknown state and measurement results
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Lemma 8.1, p. 20; Algorithm 1, p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Peeling
set_option autoImplicit false

namespace StabPauli1264.Grouped

/-- Liu--Yang--Yang, Lemma 8.1, p.20; source j corresponds to Lean j-1. -/
theorem suffix_certificate {n m : ℕ} (M : Window n m) (p : EvalLaw m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    let k := (peeled M p ε).length
    (∀ T : Finset (Fin m), IsContext M T → ∀ j : ℕ, j ≤ k →
      mass p (T ∩ remainder M p ε j) ≤ suffixWeight M p ε j) ∧
    (∀ j : ℕ, j < k → suffixWeight M p ε (j + 1) ≤ suffixWeight M p ε j) ∧
    (∀ j : ℕ, j < k → ε / 2 ≤ suffixWeight M p ε j) ∧
    k ≤ ⌊1 / (ε / 2)⌋₊ ∧ ⌊1 / (ε / 2)⌋₊ = ⌊2 / ε⌋₊ ∧
    suffixWeight M p ε k < ε / 2 ∧
    (∀ T : Finset (Fin m), IsContext M T →
      mass p (T ∩ remainder M p ε k) < ε / 2) := by sorry

end StabPauli1264.Grouped
