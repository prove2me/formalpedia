-- Prove2me | Theorems.Thm_SepMeasures_lemma_6_3
-- name    : SepMeasures.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:11:51.366264+00:00
-- url     : https://prove2.me/theorems/4396fdce-e3ac-4e1c-be41-dede68ae205a
-- title:
--   Lemma 6.3 — uniformly small non-atomic mass in thin strips
-- statement:
--   Let $d\ge1$ and let $\mu$ be a finite measure on $\mathbb R^d$ supported on the cube $[-1,1]^d$ whose non-atomic part $\mu_{na}=\mu-\sum_{x\in\mathrm{Atom}(\mu)}\mu(\{x\})\delta_x$ gives measure $0$ to every affine hyperplane. Then for every $\varepsilon>0$ there is $\eta>0$ such that
--   $$\mu_{na}\big(B(H,\eta)\big)<\varepsilon\qquad\text{for every affine hyperplane }H,$$
--   where $B(H,\eta)=\{x:\operatorname{dist}(x,H)\le\eta\}$ is the Euclidean strip of half-width $\eta$ around $H$.
--
--   The lemma lets the proof of Lemma 6.2 control, uniformly over all hyperplanes, the non-atomic mass that changes side when a hyperplane is tilted slightly.
--
--   **Formalization Note** $\mu$ is a finite measure on `EuclideanSpace ℝ (Fin d)`; the support condition is that the set of points with some coordinate outside $[-1,1]$ is $\mu$-null; $\mu_{na}$ is the restriction of $\mu$ to the complement of its atoms.
--
--   Differences from the source:
--   - generalization: µ a probability distribution supported on [−1, 1]^d (§6.2, p.47) → µ any finite measure with µ(([−1, 1]^d)ᶜ) = 0; reason: the proof uses only finiteness; probability measures are finite, so the statement specializes to the paper's
--   - encoding: µ supported on [−1, 1]^d → µ {x | ∃ i, x i ∉ [−1, 1]} = 0; reason: this is the complement of the cube
--   - encoding: µ_na := µ − Σ_{x∈Atom(µ)} µ({x})δ_x → µ.restrict (atoms µ)ᶜ with atoms µ = {x | µ {x} ≠ 0}; reason: for a finite measure the atom set is countable, so the two measures are equal
--   - encoding: µ_na(B(H, η)) < ε for real ε > 0 → nonatomic µ (strip H η) < ENNReal.ofReal ε; reason: the measure is valued in ℝ≥0∞; for ε > 0 the comparison is the same
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Lemma 6.3, p.47

import Mathlib
import Definitions.Def_SepMeasures_Families

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Lemma 6.3, p.47: let `μ` be supported on `[−1, 1]^d`
and suppose `μ_na(H) = 0` for every hyperplane `H`. Then for every `ε > 0` there is `η > 0`
with `μ_na(B(H, η)) < ε` for all hyperplanes `H`.

**Formalization Note.** `μ` is any finite measure (the paper applies the lemma to probability
measures). "Supported on `[−1, 1]^d`" is: `μ` gives measure `0` to the points having some
coordinate outside `[−1, 1]`. The strip `B(H, η)` uses the Euclidean distance to `H`. -/
theorem lemma_6_3 (d : ℕ) (hd : 1 ≤ d) (μ : Measure (E d)) [IsFiniteMeasure μ]
    (hsupp : μ {x : E d | ∃ i, x i ∉ Set.Icc (-1 : ℝ) 1} = 0)
    (hna : ∀ H : Hyp d, nonatomic μ H.set = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ H : Hyp d, nonatomic μ (strip H η) < ENNReal.ofReal ε := by sorry

end SepMeasures
