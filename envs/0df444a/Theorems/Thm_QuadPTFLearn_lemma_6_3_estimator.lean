-- Prove2me | Theorems.Thm_QuadPTFLearn_lemma_6_3_estimator
-- name    : QuadPTFLearn.lemma_6_3_estimator
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:25:20.696251+00:00
-- url     : https://prove2.me/theorems/f3293e23-6b6e-4fb8-a8fd-f65cc624e427
-- title:
--   Lemma 6.3 (estimator clause), p.63 — $\|G_\ell-\hat G\|_{op}\le\epsilon$ w.p. 99% from $d^{O(\ell)}\mathrm{poly}(\ell/\epsilon)$ samples and time; companion of `lemma_6_3`
-- statement:
--   Second sentence of Lemma 6.3. There is an algorithm such that, for every distribution $D$ over $\mathbb R^d\times\{0,1\}$ with $D_x=N(0,I)$, every $\ell\ge1$ and every $\epsilon\in(0,1)$, it draws $d^{O(\ell)}\mathrm{poly}(\ell/\epsilon)$ examples, runs in $d^{O(\ell)}\mathrm{poly}(\ell/\epsilon)$ time and outputs a matrix $\hat G$ such that, with probability at least $99\%$,
--   $$\|G_\ell-\hat G\|_{op}\le\epsilon .$$
--
--   Here $G_\ell$ is the influence matrix of `QuadPTFLearn.lemma_6_3`, the companion item stating the identity of the same lemma.
--
--   **Formalization Note** One program and one constant $C$ serve all $d,\ell,\epsilon,D$; both bounds are $C\,d^{C\ell}(\ell/\epsilon)^C$. The input is $(\ell,\epsilon)$ and $\hat G$ is output as a row-major block.
--
--   Differences from the source:
--   - reading: "there is an algorithm … using … samples and time", model unspecified → one admissible program of the deterministic arithmetic sampling real RAM (exact + − × ÷, comparisons, pointers; no √, exp, log, floor, coin; unit cost, `sample` costs d+1), chosen before every parameter and the distribution, with samples and work bounded on every sample stream; reason: the paper fixes no model and its proofs count arithmetic operations; a single uniform program with worst-case bounds is the non-weaker reading
--   - encoding: d^{O(ℓ)} poly(ℓ/ϵ) examples and time → samples and work ≤ C·d^{Cℓ}·(ℓ/ϵ)^C with one C chosen with the program; reason: ℓ/ϵ > 1, so every polynomial bound is of this form
--   - encoding: D over ℝᵈ × {0,1} with D_x = N(0, I); i.i.d. sample access → a probability law on ℝᵈ × ℝ with marginal N(0, I_d) and labels in {0,1} a.s.; the stream is i.i.d. from D, each example written as (x, y) ∈ ℝ^{d+1}; reason: the same access
--   - encoding: outputs a matrix Ĝ → the d × d block from memory cell p[1], row-major; reason: output convention
--   - encoding: an ambient dimension d → 1 ≤ d; reason: d^{O(ℓ)} vanishes at d = 0, where there are no inputs
--   - encoding: for every ϵ ∈ (0, 1), with ℓ fixed by the lemma → input list [ℓ, ϵ] in memory from cell 0, d + 1 in pointer register 0; reason: input convention of the machine; one program for every ℓ
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Lemma 6.3, second sentence ("Furthermore, …"), p.63 (PDF p.65)

import Mathlib
import Definitions.Def_QuadPTFLearn_Influence
import Definitions.Def_QuadPTFLearn_Learner

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Lemma 6.3 (estimator clause), p.63 (PDF p.65).

"Furthermore, there is an algorithm such that for every `ϵ ∈ (0, 1)`, it draws
`d^{O(ℓ)} poly(ℓ/ϵ)` [examples], runs in `d^{O(ℓ)} poly(ℓ/ϵ)` time and outputs a matrix `Ĝ` such
that with probability at least 99%, `‖G_ℓ − Ĝ‖_op ≤ ϵ`."

**Formalization Note.** One program and one constant `C`, chosen before `d, ℓ, ϵ, D`; the bound
`d^{O(ℓ)} poly(ℓ/ϵ)` is `C d^{Cℓ} (ℓ/ϵ)^C`. Input `[ℓ, ϵ]`; the output `Ĝ` is the `d × d` block,
row-major, from cell `p[1]`. `D` is any law on `ℝᵈ × ℝ` with marginal `N(0, I_d)` and labels in
`{0, 1}` almost surely, and the stream is i.i.d. from `D`. Companion of the identity
`QuadPTFLearn.lemma_6_3`. -/
theorem lemma_6_3_estimator :
    ∃ P : Program, Admissible P ∧ ∃ C : ℕ,
      ∀ d ℓ : ℕ, 1 ≤ d → 1 ≤ ℓ → ∀ ϵ : ℝ, 0 < ϵ → ϵ < 1 →
      ∀ (D : Measure (Pt d × ℝ)) [IsProbabilityMeasure D], IsBoolGaussLaw D →
        HaltsWithin P (d + 1) (initState (d + 1) [(ℓ : ℝ), ϵ])
            (C * (d : ℝ) ^ (C * ℓ) * ((ℓ : ℝ) / ϵ) ^ C)
            (C * (d : ℝ) ^ (C * ℓ) * ((ℓ : ℝ) / ϵ) ^ C) ∧
        SucceedsWP P (d + 1) (initState (d + 1) [(ℓ : ℝ), ϵ])
          (Measure.infinitePi (fun _ : ℕ => jointLaw D)) (99 / 100)
          (fun s => opNorm (Gell D ℓ - readMatrix d (outMem s) (outBase s)) ≤ ϵ) := by sorry

end QuadPTFLearn
