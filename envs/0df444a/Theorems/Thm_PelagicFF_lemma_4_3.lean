-- Prove2me | Theorems.Thm_PelagicFF_lemma_4_3
-- name    : PelagicFF.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:55.636789+00:00
-- url     : https://prove2.me/theorems/7e836053-8f52-4527-ae3a-d07f6171b6a6
-- title:
--   Lemma 4.3 — high-entropy inner-product decomposition $\langle X,Y\rangle/\sqrt N=A+S+\mathrm{err}$
-- statement:
--   Let $X$ and $Y$ be independent random variables over $\{-1,1\}^N$ with
--   $$D_\infty(X)+D_\infty(Y)=o(N).$$
--   Then the normalized inner product decomposes as
--   $$\frac{\langle X,Y\rangle}{\sqrt N}=A+S+\mathrm{err},$$
--   where $A$ and $S$ are independent, $S$ is distributed as $N^{-1/2}\sum_{i=1}^N\xi_i$ for independent uniform signs $\xi_i\in\{-1,1\}$, and $\mathbb E[\mathrm{err}^2]=o(1)$.
--
--   This is the key technical lemma of the lower bound: on every non-rare transcript, $\sqrt N\,\widehat h$ at Bob's output is such an inner product, and Lemma 3.6 then bounds the window probability.
--
--   **Formalization Note** Sequence form: dimensions $N_j\to\infty$, laws $\mu_j,\nu_j$ with $(D_\infty(\mu_j)+D_\infty(\nu_j))/N_j\to0$. For each $j$ there is a probability space carrying $(X_j,Y_j)\sim\mu_j\otimes\nu_j$ and real random variables $A_j,S_j,\mathrm{err}_j$ with the decomposition holding pointwise, $A_j$ independent of $S_j$, $S_j$ of the stated law, and $\mathbb E[\mathrm{err}_j^2]\to0$ (a lower Lebesgue integral). $A,S,\mathrm{err}$ need not be functions of $(X,Y)$.
--
--   Differences from the source:
--   - generalization: a family indexed by N → ∞ with D∞(X)+D∞(Y) = o(N) and E[err²] = o(1) → any sequence of dimensions N_j → ∞ with (D∞ μ_j + D∞ ν_j)/N_j → 0 and E[err_j²] → 0; reason: N_j = j gives the paper's form; a sequence form also applies along the subsequences used in Theorem 4.2's proof
--   - encoding: "we can decompose" with X, Y independent → ∃ a probability space per index carrying (X, Y) with law μ ⊗ ν and measurable A, S, err; reason: the decomposition lives on an extended probability space, as in the proof; same content
--   - encoding: E[err²] → ∫⁻ ofReal(err²); reason: equals the expectation of the nonnegative err²; no integrability junk
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 4.3, p.28

import Mathlib
import Definitions.Def_PelagicFF_minEntropyDeficiency
import Definitions.Def_PelagicFF_sqDist
import Definitions.Def_PelagicFF_rademacherLaw

open MeasureTheory ProbabilityTheory Filter Topology

namespace PelagicFF

/-- **Lemma 4.3 (High-entropy inner-product decomposition).** Let `X` and `Y` be independent random
variables over `{−1,1}^N` with `D∞(X) + D∞(Y) = o(N)`. Then `⟨X, Y⟩/√N = A + S + err`, where `A` and
`S` are independent, `S` is distributed as `N^{−1/2} ∑ᵢ ξᵢ` for independent uniform signs, and
`E[err²] = o(1)`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 4.3, p.28.

**Formalization Note.** Sequence form: the dimensions `N j` tend to infinity, `X_j ∼ μ_j` and
`Y_j ∼ ν_j`, and `o(·)` is a limit along `j` (the paper's `N ↦ N` is the case `N j = j`). "We can
decompose" is existential in the probability space `Ω_j`, which carries `(X_j, Y_j)` with the
product law `μ_j ⊗ ν_j` (independence with the given marginals); `A`, `S`, `err` need not be
functions of `(X, Y)`. `E[err²]` is a lower Lebesgue integral, so no integrability junk enters. -/
theorem lemma_4_3 (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ ν : ∀ j, PMF (Fin (N j) → Bool))
    (hD : Tendsto (fun j => (minEntropyDeficiency (μ j) + minEntropyDeficiency (ν j)) / N j)
      atTop (𝓝 0)) :
    ∃ (Ω : ℕ → Type) (_ : ∀ j, MeasurableSpace (Ω j)) (P : ∀ j, Measure (Ω j))
      (X Y : ∀ j, Ω j → Fin (N j) → Bool) (A S err : ∀ j, Ω j → ℝ),
      (∀ j, IsProbabilityMeasure (P j)) ∧
      (∀ j, Measurable (X j) ∧ Measurable (Y j) ∧ Measurable (A j) ∧ Measurable (S j) ∧
        Measurable (err j)) ∧
      (∀ j x y, P j {ω | X j ω = x ∧ Y j ω = y} = μ j x * ν j y) ∧
      (∀ j ω, signInner (X j ω) (Y j ω) / Real.sqrt (N j) = A j ω + S j ω + err j ω) ∧
      (∀ j, IndepFun (A j) (S j) (P j)) ∧
      (∀ j, (P j).map (S j) = rademacherLaw (N j)) ∧
      Tendsto (fun j => ∫⁻ ω, ENNReal.ofReal (err j ω ^ 2) ∂(P j)) atTop (𝓝 0) := by sorry

end PelagicFF
