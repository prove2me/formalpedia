-- Prove2me | Theorems.Thm_SepMeasures_lemma_2_4
-- name    : SepMeasures.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:10:37.959647+00:00
-- url     : https://prove2.me/theorems/05c8181b-a801-4889-8d6c-547ed633d4b9
-- title:
--   Lemma 2.4 — $\Pr[K \text{ strictly separates } X,Y]=(1-p_Kq_K)/2$
-- statement:
--   Let $d\ge1$, let $X\sim\mu$ and $Y\sim\nu$ be independent random vectors in $\mathbb R^d$, and let $K$ be an oriented hyperplane with $\mu(K)=\nu(K)=0$. With $p_K=\mathbb E_\mu[\sigma_K]$ and $q_K=\mathbb E_\nu[\sigma_K]$,
--   $$\Pr[K\text{ strictly separates }X,Y]=\frac{1-p_Kq_K}{2}.$$
--
--   It expresses separation probabilities through sign expectations, the form in which bisection conditions enter the proofs of Theorems 3.2 and 3.3.
--
--   **Formalization Note** The probability is $(\mu\otimes\nu)(\mathrm{Sep}(K))$ as a real number.
--
--   Differences from the source:
--   - encoding: independent X ∼ µ, Y ∼ ν; Pr[·]; E_µ[σ_K] → the product measure µ.prod ν and its real-valued measure (µ.prod ν).real; Bochner integrals ∫ σ_K dµ; reason: σ_K is bounded and measurable, so the integrals are the expectations; the product measure is the law of an independent pair
-- source:
--   Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, Separating Measures by Hyperplanes (manuscript, STOC 2027 submission, sha256 96a8692407ff1815980863f3baa9c5d7b90ba27e781ed19063306f67d26fa82f), Lemma 2.4, p.13

import Mathlib
import Definitions.Def_SepMeasures_Hyp

open MeasureTheory

namespace SepMeasures

/-- Correa–Griesbach–Harb–Hommelsheim–Jlibene–Livanos–Solan, *Separating Measures by Hyperplanes*
(manuscript, sha256 96a86924…fa82f), Lemma 2.4, p.13: let `X ∼ μ` and `Y ∼ ν` be
independent, `K` a hyperplane with `μ(K) = ν(K) = 0`, `p_K := E_μ[σ_K]` and `q_K := E_ν[σ_K]`.
Then `Pr[K strictly separates X, Y] = (1 − p_K q_K)/2`.

**Formalization Note.** Independence is the product measure `μ.prod ν`; the probability is
`(μ.prod ν).real (Sep K)`, with `Sep K` the pairs strictly separated by `K`. -/
theorem lemma_2_4 (d : ℕ) (hd : 1 ≤ d) (μ ν : Measure (E d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Hyp d) (hμ : μ K.set = 0) (hν : ν K.set = 0) :
    (μ.prod ν).real (Sep K) = (1 - (∫ x, K.sign x ∂μ) * (∫ y, K.sign y ∂ν)) / 2 := by sorry

end SepMeasures
