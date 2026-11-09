-- Prove2me | Theorems.Thm_PerturbedWF_lemma_3_1
-- name    : PerturbedWF.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:39:21.744386+00:00
-- url     : https://prove2.me/theorems/da45dbf9-68d9-432b-aea6-e45a1e593f19
-- title:
--   Lemma 3.1: $W_0^*(v)-W_T^*(v)\le\mathrm{OPT}+\langle v,x_0-x_T\rangle$, and $\mathbb E[W_0^*(v)]-\mathbb E[W_T^*(v)]\le\mathrm{OPT}$ for centred $v$
-- statement:
--   Let $\mathcal C$ be a configuration space over a finite metric $d$, let $x_0\in\mathcal C$ be the initial state with $W_0(x)=\|x-x_0\|$, let $W_T:\mathcal C\to\mathbb R_{\ge0}\cup\{\infty\}$, and let $x_T\in\mathcal C$ satisfy $W_T(x_T)=\mathrm{OPT}$. Then:
--   1. for every $v\in B^*$,
--   $$W_0^*(v)-W_T^*(v)\le\mathrm{OPT}+\langle v,x_0-x_T\rangle;$$
--   2. for a random $v\in B^*$ with $\mathbb E[v]=0$, both $W_0^*(v)$ and $W_T^*(v)$ are integrable and
--   $$\mathbb E[W_0^*(v)]-\mathbb E[W_T^*(v)]\le\mathrm{OPT}.$$
--
--   This compares the algorithm's potential, the conjugate of the work function, with the optimal offline cost.
--
--   **Formalization Note.** Part 1 is stated additively in `EReal`: $W_0^*(v)\le W_T^*(v)+(\mathrm{OPT}+\langle v,x_0-x_T\rangle)$. In part 2, $v$ has law $\mu$, a probability measure on $\mathbb R^n$ with $v\in B^*$ almost surely, integrable coordinates and $\mathbb E[v_i]=0$; the conclusion includes the integrability of both conjugates (as real numbers), so the Bochner integrals are the true expectations.
--
--   Differences from the source:
--   - generalization: W_T the final work function, OPT = min_C W_T and x_T a minimizer → any W_T : C → ℝ_{≥0} ∪ {∞} and any x_T ∈ C, opt ∈ ℝ with W_T(x_T) = opt; reason: the work function and OPT satisfy these hypotheses, so the statement specializes to the paper's; the proof uses nothing else
--   - encoding: W₀*(v) − W_T*(v) ≤ OPT + ⟨v, x₀ − x_T⟩ → conj W₀ v ≤ conj W_T v + (opt + ⟨v, x₀ − x_T⟩) in EReal; reason: the same inequality without subtracting EReal values; both conjugates are finite here
--   - reading: a random v ∈ B* with E[v] = 0 → a probability law μ with v ∈ B* a.s., every coordinate integrable and ∫ v_i dμ = 0; integrability of both conjugates is part of the conclusion; reason: E[v] = 0 presupposes that the expectation of v exists
--   - encoding: v ∈ B* = {v : ‖v‖* ≤ 1} → v ∈ dualBall d, i.e. |v_i − v_j| ≤ d(i, j) for all i, j; reason: the characterization of B* stated after (2.2), p.5 (v ∈ B* iff |v_i − v_j| ≤ d(i, j)); the same set
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma 3.1, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_PerturbedWF_WClass

namespace PerturbedWF

open MeasureTheory

/-- **Lemma 3.1** (p.8, PDF p.9). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

Let `x₀ ∈ C` be the initial state, `W₀(x) = ‖x − x₀‖`, and let `x_T ∈ C` satisfy
`W_T(x_T) = OPT`.
1. For any `v ∈ B*`, `W₀^*(v) − W_T^*(v) ≤ OPT + ⟨v, x₀ − x_T⟩`.
2. For a random `v ∈ B*` with `E[v] = 0`, `E[W₀^*(v)] − E[W_T^*(v)] ≤ OPT`.

**Formalization Note.** Stated for any configuration space `C`, any `W_T : C → ℝ_{≥0} ∪ {∞}` and
any `x_T ∈ C` with `W_T(x_T) = opt` (the proof uses only these properties of the final work
function and of `OPT`). Part 1 is written additively in `EReal`. In part 2, `v` has law `μ`, a
probability measure on `ℝ^ι` with `v ∈ B*` almost surely, integrable coordinates and `E[v_i] = 0`;
the conclusion includes the integrability of both conjugates, so the Bochner integrals are the
true expectations. -/
theorem lemma_3_1 {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (hC : IsConfigSpace C) (d : ι → ι → ℝ) (hd : IsFinMetric d)
    (x₀ : ι → ℝ) (hx₀ : x₀ ∈ C) (WT : (ι → ℝ) → EReal) (hWT : ∀ x ∈ C, 0 ≤ WT x)
    (xT : ι → ℝ) (hxT : xT ∈ C) (opt : ℝ) (hopt : WT xT = opt) :
    (∀ v ∈ dualBall d,
        conj C (fun x => ((transNorm d (x - x₀) : ℝ) : EReal)) v ≤
          conj C WT v + ((opt + dot v (x₀ - xT) : ℝ) : EReal)) ∧
      ∀ μ : Measure (ι → ℝ), IsProbabilityMeasure μ → (∀ᵐ v ∂μ, v ∈ dualBall d) →
        (∀ i, Integrable (fun v : ι → ℝ => v i) μ) → (∀ i, ∫ v, v i ∂μ = 0) →
        Integrable (fun v => (conj C (fun x => ((transNorm d (x - x₀) : ℝ) : EReal)) v).toReal) μ ∧
          Integrable (fun v => (conj C WT v).toReal) μ ∧
          (∫ v, (conj C (fun x => ((transNorm d (x - x₀) : ℝ) : EReal)) v).toReal ∂μ) -
              (∫ v, (conj C WT v).toReal ∂μ) ≤ opt := by sorry

end PerturbedWF
