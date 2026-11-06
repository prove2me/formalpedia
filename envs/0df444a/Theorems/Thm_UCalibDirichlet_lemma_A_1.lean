-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_A_1
-- name    : UCalibDirichlet.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:25:10.699853+00:00
-- url     : https://prove2.me/theorems/acdcc7fb-ff34-4840-ac36-0bc749d7ec40
-- title:
--   Lemma A.1 — converse inequality for Bernstein polynomials (after Sangüesa)
-- statement:
--   There is a universal constant $C_B$ such that for every integer $n\ge1$ and every continuous $G:[0,1]\to\mathbb R$,
--   $$\sup_{p\in[0,1]}p(1-p)\big|(B_nG)''(p)\big|\le C_B\,n\,\|B_nG-G\|_\infty,$$
--   where $B_nG(p)=\mathbb E_{S\sim\mathrm{Bin}(n,p)}[G(S/n)]$ and $\|\cdot\|_\infty$ is the supremum norm on $[0,1]$.
--
--   The weighted second derivative of a Bernstein polynomial is controlled by its approximation error; this is the input from Sangüesa (2001) used to prove Lemma 1.7.
--
--   Differences from the source:
--   - encoding: universal C_B; sup over p ∈ [0,1] → ∃ C_B before n and G; the bound for every p ∈ [0,1]; reason: universal = independent of n and G; a supremum is at most a bound iff every value is
--   - encoding: G ∈ C([0,1]), (B_nG)″ → G : ℝ → ℝ continuous on [0,1]; iteratedDeriv 2 of the polynomial bern G n; reason: only values on [0,1] enter B_nG
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma A.1, display (36), p.23

import Mathlib
import Definitions.Def_UCalibDirichlet_bern

namespace UCalibDirichlet

/-- **Lemma A.1 (converse inequality for Bernstein polynomials, after Sangüesa [2001]).**
Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027 submission), Lemma A.1, display (36),
p.23: "There is a universal constant `C_B` such that, for every integer `n ≥ 1` and every
`G ∈ C([0, 1])`, `sup_{p∈[0,1]} p(1 − p) |(B_n G)″(p)| ≤ C_B n ‖B_n G − G‖_∞`, (36) where
`B_n G(p) = E_{S∼Bin(n,p)}[G(S/n)]` is the `n`-th Bernstein polynomial for `G`."

**Formalization Note.** `C_B` is one `∃` before `n` and `G`. `G ∈ C([0,1])` is `G : ℝ → ℝ` continuous
on `[0, 1]`. `(B_n G)″` is the second derivative of the polynomial `bern G n`. The supremum on the
left is stated pointwise (`∀ p ∈ [0, 1]`), which is equivalent. `‖B_n G − G‖_∞` is the supremum of
`|B_n G − G|` over `[0, 1]`, a bounded family (continuous on a compact set). -/
theorem lemma_A_1 : ∃ C_B : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ G : ℝ → ℝ, ContinuousOn G (Set.Icc 0 1) →
    ∀ p ∈ Set.Icc (0 : ℝ) 1,
      p * (1 - p) * |iteratedDeriv 2 (bern G n) p| ≤
        C_B * n * ⨆ x : Set.Icc (0 : ℝ) 1, |bern G n x - G x| := by sorry

end UCalibDirichlet
