-- Prove2me | Theorems.Thm_PerturbedWF_lemma_2_3
-- name    : PerturbedWF.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:40:02.703403+00:00
-- url     : https://prove2.me/theorems/b3b2b57d-f778-4828-b80e-c3c173815359
-- title:
--   Lemma 2.3: $W^*(v)=\max_{x\in\mathrm{supp}(W)}\{\langle v,x\rangle-W(x)\}$ for $v\in B^*$
-- statement:
--   Let $\mathcal C$ be a configuration space over a finite metric $d$ and $W\in\mathcal W(\mathcal C)$. For every $v\in B^*$ a maximizer of (2.4) exists in the support of $W$:
--   $$W^*(v)=\max_{x\in\mathrm{supp}(W)}\{\langle v,x\rangle-W(x)\}.$$
--
--   This is what lets the algorithm move only to support points, where the work function has just been paid for.
--
--   **Formalization Note.** Stated as: some $x\in\mathrm{supp}(W)$ maximizes $\langle v,\cdot\rangle-W$ over all of $\mathcal C$, and $W^*(v)$ equals its value. This is equivalent to the display, since $\mathrm{supp}(W)\subseteq\mathcal C$.
--
--   Differences from the source:
--   - encoding: W*(v) = max over supp(W) of ⟨v, x⟩ − W(x) → ∃ x ∈ supp(W) maximizing ⟨v, ·⟩ − W over C, with conj W v equal to its value; reason: equivalent because supp(W) ⊆ C; 'max' asserts attainment
--   - encoding: v ∈ B* = {v : ‖v‖* ≤ 1} → v ∈ dualBall d, i.e. |v_i − v_j| ≤ d(i, j) for all i, j; reason: the characterization of B* stated after (2.2), p.5 (v ∈ B* iff |v_i − v_j| ≤ d(i, j)); the same set
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Lemma 2.3 and the sentence before it, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_PerturbedWF_WClass

namespace PerturbedWF

/-- **Lemma 2.3** (p.6, PDF p.7), with the sentence before it ("For every `v ∈ B*`, a maximizer of
(2.4) always exists in the support of `W`"). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

For `W ∈ W(C)` and any `v ∈ B*`, `W*(v) = max_{x ∈ supp(W)} {⟨v, x⟩ − W(x)}`.

**Formalization Note.** Stated as: some `x ∈ supp(W)` maximizes `⟨v, ·⟩ − W` over all of `C`,
and `W*(v)` equals the value at `x` (equivalent to the displayed identity, since
`supp(W) ⊆ C`). -/
theorem lemma_2_3 {ι : Type} [Fintype ι] [DecidableEq ι] (C : Set (ι → ℝ))
    (hC : IsConfigSpace C) (d : ι → ι → ℝ) (hd : IsFinMetric d) (W : (ι → ℝ) → EReal)
    (hW : WClass C d W) (v : ι → ℝ) (hv : v ∈ dualBall d) :
    ∃ x ∈ supp C d W, conj C W v = ((dot v x : ℝ) : EReal) - W x ∧
      ∀ y ∈ C, ((dot v y : ℝ) : EReal) - W y ≤ ((dot v x : ℝ) : EReal) - W x := by sorry

end PerturbedWF
