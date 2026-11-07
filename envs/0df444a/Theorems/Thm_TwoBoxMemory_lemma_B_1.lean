-- Prove2me | Theorems.Thm_TwoBoxMemory_lemma_B_1
-- name    : TwoBoxMemory.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:43.035346+00:00
-- url     : https://prove2.me/theorems/c9e22c78-d24d-4a55-b37e-a70d6989a72b
-- title:
--   Lemma B.1 — exact lasso prefix and (B.6)
-- statement:
--   Throughout, $(r,s,\beta,D)$ is a **non-tie positive saddle with irrational logarithmic failure ratio**: $r,s\in(0,1)$ are the failure probabilities at locations $A$ and $B$ ($p=1-r$, $t=1-s$), $\log r/\log s$ is irrational, $\beta>0$, $\beta r^i\neq s^j$ for all $i,j\ge0$, $u=1/p-H_B>0$, $v=1/t-H_A>0$ and $D>0$; the cost of command $A$ is the saddle cost $C=Dv/u$, and $W$ is the greedy word. Let $M\ge1$.
--
--   1. No deterministic controller with a pure initial label and at most $M$ labels agrees with $W$ on more than $H_M$ initial symbols, and some such controller agrees with $W$ on exactly $H_M$ initial symbols.
--   2. (B.6) holds:
--   $$H_M\ge M,\qquad H_M\ge D_M+1,\qquad H_M\le M+D_M<F_M\le 2H_M .$$
--
--   This identifies $H_M$ as the memory horizon of deterministic lassos.
--
--   Differences from the source:
--   - encoding: a deterministic controller agrees with W on n initial symbols → its cylinder probability of W_0⋯W_{n−1} is 1 (exactness: probability 0 for the length H_M + 1 prefix); reason: a deterministic controller emits one word, whose length-n cylinder has probability 1
--   - encoding: (B.6) for the lemma's budget M → M ≥ 1; reason: the maxima over pairs i < j ≤ M are defined only for M ≥ 1
--   - encoding: commands A, B; risks in [0, ∞] → commands `Fin 2` with 0 = A, 1 = B; risks in `ℝ≥0∞`; reason: Lean convention; same instances
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), Lemma B.1 and (B.6), p.22 (PDF 24); §7, p.9 (PDF 11)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Saddle
import Definitions.Def_TwoBoxMemory_Profile
import Definitions.Def_TwoBoxMemory_Constants
open MeasureTheory

namespace TwoBoxMemory

/-- Lemma B.1 (Exact lasso prefix). At a non-tie positive saddle and for `M ≥ 1`: among
deterministic controllers with a pure initial label and at most `M` labels, the maximum number of
initial symbols that can agree with `W` is exactly `H_M`; and (B.6)
`H_M ≥ M`, `H_M ≥ D_M + 1`, `H_M ≤ M + D_M < F_M ≤ 2 H_M`.

**Formalization Note.** A deterministic controller agrees with `W` on `n` initial symbols iff its
cylinder probability of `W_0 ⋯ W_{n−1}` is `1`. "Exactly" is stated as: no such controller agrees
on more than `H_M` symbols, and one agrees on exactly `H_M` (its probability of the length-`(H_M+1)`
prefix is `0`). `M ≥ 1` makes the set of pairs `i < j ≤ M` nonempty.

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
Lemma B.1 and (B.6), p.22 (PDF 24); §7, p.9 (PDF 11).

Standing setting: commands are `Fin 2` with `0 = A`, `1 = B`; risks are in `ℝ≥0∞`; `gap` is
`Δ_M = V_M − V` as a real number. -/
theorem lemma_B_1 (r s β D : ℝ) (hS : IsSaddle r s β D) (M : ℕ) (hM : 1 ≤ M) :
    (∀ m : ℕ, m ≤ M → ∀ κ : Controller m, IsDeterministic κ → ∀ n : ℕ,
      cylProb κ (wordPrefix (greedyWord r s β) n) = 1 → n ≤ profH (greedyWord r s β) M) ∧
    (∃ m ≤ M, ∃ κ : Controller m, IsDeterministic κ ∧
      cylProb κ (wordPrefix (greedyWord r s β) (profH (greedyWord r s β) M)) = 1 ∧
      cylProb κ (wordPrefix (greedyWord r s β) (profH (greedyWord r s β) M + 1)) = 0) ∧
    M ≤ profH (greedyWord r s β) M ∧ profD (greedyWord r s β) M + 1 ≤ profH (greedyWord r s β) M ∧
    profH (greedyWord r s β) M ≤ M + profD (greedyWord r s β) M ∧ M + profD (greedyWord r s β) M < profF (greedyWord r s β) M ∧
    profF (greedyWord r s β) M ≤ 2 * profH (greedyWord r s β) M := by sorry

end TwoBoxMemory
