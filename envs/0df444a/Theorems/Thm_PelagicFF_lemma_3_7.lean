-- Prove2me | Theorems.Thm_PelagicFF_lemma_3_7
-- name    : PelagicFF.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:39.717284+00:00
-- url     : https://prove2.me/theorems/079b805e-37e5-4e09-bb37-607e5dfa7a4d
-- title:
--   Lemma 3.7 — Pelagic implies the window $a/\sqrt s\le|\widehat w(y)|\le3a/\sqrt s$ w.h.p.
-- statement:
--   Let $s=2^t$ and $t\to\infty$. Let $(W,U)$ be coupled random variables over $\{-1,1\}^s$ with $U\sim\mathrm{Unif}(\{-1,1\}^s)$ and
--   $$\frac1s\,\mathbb E\|W-U\|_2^2=o(1).$$
--   Regard $W$ as the truth table of $w:\{0,1\}^t\to\{-1,1\}$. Then with probability $1-o(1)$, every $y\in\{0,1\}^t$ at which $w$ satisfies the Pelagic condition also satisfies the window condition
--   $$\frac a{\sqrt s}\ \le\ |\widehat w(y)|\ \le\ \frac{3a}{\sqrt s},\qquad a=\sqrt{2/3}.$$
--
--   Applied with $W=U=F\odot G$ it converts the window bound into the failure of every protocol of cost $o(2^n)$.
--
--   **Formalization Note** Sequence form: $t_j\to\infty$; the coupling is a law $\pi_j$ on pairs of truth tables on $\{0,1\}^{t_j}$ with uniform second marginal; "with probability $1-o(1)$" means that the $\pi_j$-probability of the event tends to $1$.
--
--   Differences from the source:
--   - generalization: t → ∞ with o(1) terms → any sequence t_j → ∞, hypothesis and conclusion as limits along j; reason: t_j = j gives the paper's form
--   - encoding: Boolean functions with values in {−1,1} → Bool-valued functions read through OAI.Cotype.sign (false ↦ 1, true ↦ −1); reason: a bijection of value sets; same instances
--   - encoding: coupled random variables (W, U) with U uniform → a PMF π_j on pairs of truth tables whose second marginal is uniform; reason: Definition 2.3; same couplings
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.7, p.24

import Mathlib
import Definitions.Def_PelagicFF_PFF
import Definitions.Def_PelagicFF_sqDist

open OAI.Cotype Filter Topology
open Classical

namespace PelagicFF

/-- **Lemma 3.7.** Let `s = 2^t`, `t → ∞`, and let `(W, U)` be coupled random variables over
`{−1,1}^s` with `U ∼ Unif({−1,1}^s)` and `(1/s) E‖W − U‖₂² = o(1)`. Regard `W` as the truth table of
`w : {0,1}^t → {−1,1}`. Then with probability `1 − o(1)`, every `y` satisfying the Pelagic condition
also satisfies the window condition `a/√s ≤ |ŵ(y)| ≤ 3a/√s`, where `a = √(2/3)`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.7, p.24.

**Formalization Note.** Sequence form: `t j → ∞`; the coupling is a law `π_j` on pairs of truth
tables `BoolFn (t j)` with uniform second marginal; "with probability `1 − o(1)`" is convergence to
`1` of the `π_j`-probability of the event. -/
theorem lemma_3_7 (t : ℕ → ℕ) (ht : Tendsto t atTop atTop)
    (π : ∀ j, PMF (BoolFn (t j) × BoolFn (t j)))
    (hU : ∀ j, (π j).map Prod.snd = PMF.uniformOfFintype (BoolFn (t j)))
    (hclose : Tendsto (fun j => ((2 : ℝ) ^ t j)⁻¹ * ∑ p, (π j p).toReal * sqDist p.1 p.2)
      atTop (𝓝 0)) :
    Tendsto (fun j => ∑ p ∈ Finset.univ.filter (fun p : BoolFn (t j) × BoolFn (t j) =>
        ∀ y, IsPelagic (fun x => sign (p.1 x)) y →
          Real.sqrt (2 / 3) / Real.sqrt (2 ^ t j) ≤ |OAI.Cotype.fourier (fun x => sign (p.1 x)) y| ∧
          |OAI.Cotype.fourier (fun x => sign (p.1 x)) y| ≤ 3 * Real.sqrt (2 / 3) / Real.sqrt (2 ^ t j)),
        (π j p).toReal) atTop (𝓝 1) := by sorry

end PelagicFF
