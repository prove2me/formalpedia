-- Prove2me | Theorems.Thm_WassChanceCvx_lemma_2_atomless
-- name    : WassChanceCvx.lemma_2_atomless
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:41.549074+00:00
-- url     : https://prove2.me/theorems/1883dd54-fd21-4798-908a-5fa0420d3798
-- title:
--   Lemma 2 (corrected: ℙ absolutely continuous) — $d(\zeta,\mathcal S^c(x))$ and $f(x,\zeta)$ are atomless
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel σ-algebra and $\mu$ a Haar (Lebesgue) measure on it, and let $\mathbb P$ be an α-concave probability measure on $E$ that is absolutely continuous with respect to $\mu$. Let $A(x)$, $b(x)$ depend affinely on $x$, $\zeta\sim\mathbb P$. Then for every $x$:
--
--   1. $\mathbb P\bigl[d(\zeta,\mathcal S^c(x))=y\bigr]=0$ for all $y>0$;
--   2. if $A(x)\ne0$, then $\mathbb P\bigl[f(x,\zeta)=y\bigr]=0$ for all $y\in\mathbb R$.
--
--   Atomlessness of the slack is what lets the paper pass from the CVaR constraint (3) to the integral constraint (5).
--
--   **Formalization Note** $d$ is valued in $[0,\infty]$ and equals $+\infty\ne y$ when the unsafe set is empty, so clause 1 holds for every $x$. Clause 2 needs $A(x)\ne0$, where $f(x,\cdot)$ is defined.
--
--   Differences from the source:
--   - correction: $\mathbb P$ α-concave only → $\mathbb P$ α-concave and `P ≪ μ` for an additive Haar measure $\mu$ on $E$; reason: the printed lemma is false: $\mathbb P=\delta_0$ on $\mathbb R$ is α-concave for every α, and with one row $a=1$, $b(x)=x$ one gets $f(0,\zeta)=-\zeta$ and $\mathbb P[f(0,\zeta)=0]=1$; the proof (B.2) uses exactly that $\mathbb P$ is absolutely continuous with respect to Lebesgue measure
--   - encoding: ℝ^q (written ℝ^m in §3.1) with an arbitrary norm ‖·‖; rows $a_i$ with dual norm $\|a_i\|_*$ → a finite-dimensional real normed space $E$ with its Borel σ-algebra; rows are continuous linear functionals on $E$, $\|a_i\|_*$ their operator norm; reason: the same objects: ℝ^q with any norm is such a space and the dual norm is the operator norm
--   - encoding: decision $x\in\mathbb R^n$; $A(x)\in\mathbb R^{m\times q}$ and $b(x)\in\mathbb R^m$ affine in $x$ → `Fin n → ℝ`; `A` an affine map into $k$-tuples of functionals on $E$, `b` an affine map into $\mathbb R^k$; reason: same data; $k$ rows of $A(x)$, each a functional on $E$
--   - reading: $\mathcal P_0$ is the set of all probability distributions; $\Xi$ is the support of $\xi$ → all Borel probability measures on $E$; $\Xi=E$; reason: p.3 takes all probability distributions, and the proof of Theorem 1 (p.8) uses $d(\zeta,\mathcal S^c(x))=(f(x,\zeta))^+$ for every $\zeta\in\mathbb R^m$, which holds only when the unsafe set is taken in all of $\mathbb R^m$
--   - encoding: Definition 2: $\mathbb P$ on the Lebesgue subsets of a convex $\Omega$, Borel $A,B\subseteq\Omega$, $\mathbb P(\theta A+(1-\theta)B)\ge m_\alpha(\mathbb P(A),\mathbb P(B);\theta)$ → `IsAlphaConcaveMeasure α P`: all measurable $A,B\subseteq E$, $P$ evaluated on $\theta A+(1-\theta)B$ as Mathlib's outer measure, values compared through `toReal`; reason: equivalent: $\theta A+(1-\theta)B$ is analytic, so its outer measure is its Lebesgue (completion) measure; $\Omega$ is immaterial because $m_\alpha$ is nondecreasing in each argument; probabilities are finite
--   - encoding: $\alpha\in\overline{\mathbb R}$ → `α : EReal`; reason: same values $[-\infty,+\infty]$
--   - encoding: the $f$-clause for all $x$ → the $f$-clause for $x$ with $A(x)\ne0$; reason: $f(x,\cdot)$ is undefined when $A(x)=0$
--   - encoding: real distance $d(\zeta,\mathcal S^c(x))$ → `unsafeDist`, `Metric.infEDist` valued in $[0,\infty]$, with $y$ as `ENNReal.ofReal y`; reason: for $y>0$ the event is the same; an empty unsafe set gives $+\infty\ne y$
--   - encoding: $\min_{i\in[m]\setminus I(x)}$ → real infimum over the finite subtype of nonzero rows (`slack`); reason: nonempty under $A(x)\ne0$, so it is the minimum
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Lemma 2, p.7; proof in Appendix B.2, p.36

import Mathlib
import Definitions.Def_WassChanceCvx_IsAlphaConcaveMeasure
import Definitions.Def_WassChanceCvx_unsafeDist
import Definitions.Def_WassChanceCvx_slack

open MeasureTheory

namespace WassChanceCvx

/-- **Lemma 2 (atomless distance and slack), corrected.**
Shen, Jiang, arXiv:2111.02486v2, Lemma 2, p.7: "If the reference distribution `ℙ` is α-concave,
then for all `x`, `ℙ[d(ζ, 𝒮ᶜ(x)) = y] = 0` for all `y > 0` and `ℙ[f(x, ζ) = y] = 0` for all
`y ∈ ℝ`."

**Correction.** The hypothesis "`ℙ` is absolutely continuous with respect to Lebesgue measure",
which the proof (Appendix B.2, p.36) uses, is added: `P ≪ μ` for an additive Haar measure `μ` on
`E` (Lebesgue measure on `ℝ^q`). As printed the lemma is false: `ℙ = δ₀` on `ℝ` is α-concave for
every `α`, and with one row `a = 1`, `b(x) = x` one has `f(0, ζ) = −ζ` and `ℙ[f(0, ζ) = 0] = 1`.

**Formalization Note.** The `f`-clause is stated for `x` with `A(x) ≠ 0`, where `f(x, ·)` is
defined. The `d`-clause holds for every `x`; `d` is `[0, ∞]`-valued and equals `+∞ ≠ y` when the
unsafe set is empty. -/
theorem lemma_2_atomless
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {n k : ℕ}
    (A : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → StrongDual ℝ E)) (b : (Fin n → ℝ) →ᵃ[ℝ] (Fin k → ℝ))
    (P : Measure E) [IsProbabilityMeasure P] (α : EReal) (hP : IsAlphaConcaveMeasure α P)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hac : P ≪ μ) (x : Fin n → ℝ) :
    (∀ y : ℝ, 0 < y → P {ζ | unsafeDist (A x) (b x) ζ = ENNReal.ofReal y} = 0) ∧
      (A x ≠ 0 → ∀ y : ℝ, P {ζ | slack (A x) (b x) ζ = y} = 0) := by sorry

end WassChanceCvx
