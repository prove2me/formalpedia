-- Prove2me | Theorems.Thm_SongZhangKLS_lemma_3_8
-- name    : SongZhangKLS.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:20.352361+00:00
-- url     : https://prove2.me/theorems/89d33db6-7940-4415-9c0b-244b2cc27bcb
-- title:
--   Lemma 3.8 — quadratic forms: $\mathrm{Var}_\mu[X^\top BX]\le 8\,\mathrm{tr}[B^2]$ for isotropic log-concave $\mu$
-- statement:
--   Let $X$ have an isotropic log-concave probability distribution $\mu$ on $\mathbb R^n$. For every real symmetric matrix $B\in\mathbb R^{n\times n}$,
--   $$\mathrm{Var}_\mu\big[X^\top BX\big]\le 8\cdot\mathrm{tr}[B^2].$$
--
--   This is Theorem 1.2 of Letwin (cited as [Let26]); it is the degree-two base case of the double induction behind Theorem 4.1.
--
--   **Formalization Note** $X^\top BX=\sum_{i,j}B_{ij}x_ix_j$. The variance lies in $[0,\infty]$, so the bound includes that the quadratic form has finite variance.
--
--   Differences from the source:
--   - encoding: log-concave: $\mu(sA+(1-s)B)\ge\mu(A)^s\mu(B)^{1-s}$ for compact $A,B$ and $0\le s\le1$ → the published `FunctionalInequalities.KLS.LogConcave` (the same inequality for $0<s<1$); reason: the endpoints $s\in\{0,1\}$ are trivial for every measure under the paper's conventions, while the literal $s=0$, $A=\emptyset$ case with the convention $0^0=1$ would exclude every measure; same class
--   - encoding: isotropic: $\int x\,d\mu=0$ and $\int x\otimes x\,d\mu=I_n$ → the published `FunctionalInequalities.KLS.Isotropic` (finite second moment, mean $0$, centered covariance operator the identity); reason: finite second moments are implicit in the source's definition; same measures
--   - encoding: $\mathrm{Var}_\mu[\cdot]$ → `evariance` (variance in $[0,\infty]$); reason: Lean convention; a finite bound on `evariance` is the source's variance bound, without the junk value $0$ of the real variance outside $L^2$
-- source:
--   Z. Song, X. Zhang, An O(1) Bound for the KLS Constant, arXiv:2610.01447 (preprint; version of October 2026, sha256 c7d2264f…8a6c), Lemma 3.8 (Theorem 1.2 of [Let26]), p.15

import Mathlib
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic

open MeasureTheory ProbabilityTheory

namespace SongZhangKLS

/-- **Lemma 3.8 (Quadratic forms, Theorem 1.2 of [Let26])**, p.15, of Song, Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447 (version of October 2026,
sha256 c7d2264f…8a6c).

Let `X` have an isotropic log-concave probability distribution `µ` on `ℝⁿ`. For every real
symmetric matrix `B ∈ ℝ^{n×n}`, `Var_µ[XᵀBX] ≤ 8 · tr[B²]`.

**Formalization Note.** Log-concavity and isotropy are the published
`FunctionalInequalities.KLS.LogConcave` and `FunctionalInequalities.KLS.Isotropic`. `XᵀBX` is
`Σ_{i,j} B_{ij} x_i x_j`; the variance is `evariance` (in `ℝ≥0∞`), so the bound also asserts that
the quadratic form has finite variance. -/
theorem lemma_3_8 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hlc : FunctionalInequalities.KLS.LogConcave μ) (hiso : FunctionalInequalities.KLS.Isotropic μ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) :
    evariance (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, B i j * x i * x j)
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (8 * (B * B).trace) := by sorry

end SongZhangKLS
