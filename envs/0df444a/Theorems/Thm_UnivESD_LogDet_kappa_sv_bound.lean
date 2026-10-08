-- Prove2me | Theorems.Thm_UnivESD_LogDet_kappa_sv_bound
-- name    : UnivESD.LogDet.kappa_sv_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:04.016666+00:00
-- url     : https://prove2.me/theorems/01406067-7ca2-4574-8c63-3ba0acc82422
-- title:
--   §8, p. 2057 — a.s. $\frac1n\sum_{(1-\kappa)n<i\le n}\log\frac1{\sigma_i}\le O(\kappa\log\frac1\kappa)$ eventually
-- statement:
--   Let $A_n=M_n+X_n$ be as in Theorem 1.5, fix $z\in\mathbb C$, and write $\sigma_i=\sigma_i\big(\tfrac1{\sqrt n}A_n-zI\big)$. There is a constant $C$ such that for every fixed $0<\kappa<1/2$, almost surely, for all but finitely many $n$, $\sigma_n>0$ and
--   $$\frac1n\sum_{(1-\kappa)n<i\le n}\log\frac1{\sigma_i}\le C\,\kappa\log\frac1\kappa .$$
--
--   It bounds the total logarithmic contribution of the $\approx\kappa n$ smallest singular values, uniformly in $\kappa$; via Lemma A.3 it passes to the eigenvalues of smallest modulus.
--
--   **Formalization Note** The paper's $O(\kappa\log(1/\kappa))$ is a constant $C$ chosen before $\kappa$ (it may depend on $z$, $x$ and $M_n$); with $C$ depending on $\kappa$ the bound would carry no information, and the next step of the proof ($|\lambda_{\lfloor(1-\kappa)n\rfloor}|\ge\kappa^{O(1)}$) needs it uniform. The integer range $(1-\kappa)n<i\le n$ is $\lfloor(1-\kappa)n\rfloor<i\le n$. $\sigma_n>0$ is part of the conclusion so that no term $\log(1/\sigma_i)$ is Lean's junk $\log(1/0)=0$. Singular values are one-based.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2057 (PDF 35), §8, proof of Theorem 1.15, (i) ⇒ (ii), first display

import Mathlib
import Definitions.Def_UnivESD_LogDet_Basic
import Definitions.Def_UnivESD_LogDet_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace UnivESD.LogDet

/-- §8, proof of (i) ⇒ (ii), p. 2057, first display. For `A_n` as in Theorem 1.5 and every
`z ∈ ℂ` there is a constant `C` such that for every fixed `0 < κ < 1/2`, almost surely, for all
but finitely many `n`: `σ_n > 0` and
`(1/n) Σ_{(1−κ)n < i ≤ n} log(1/σ_i) ≤ C κ log(1/κ)`, with `σ_i = σ_i(A_n/√n − zI)` one-based.
The index set `(1−κ)n < i ≤ n` of integers is `Finset.Ioc ⌊(1−κ)n⌋₊ n`. -/
theorem kappa_sv_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs : ℕ → ℕ → Ω → ℂ) (hxs : IIDArray P xs)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : HSBound M) (z : ℂ) :
    ∃ C : ℝ, ∀ κ : ℝ, 0 < κ → κ < 1 / 2 →
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
        0 < sv (shiftA M xs z n ω) n ∧
        (1 / (n : ℝ)) * ∑ i ∈ Finset.Ioc ⌊(1 - κ) * (n : ℝ)⌋₊ n,
            Real.log (1 / sv (shiftA M xs z n ω) i) ≤ C * κ * Real.log (1 / κ) := by sorry

end UnivESD.LogDet
