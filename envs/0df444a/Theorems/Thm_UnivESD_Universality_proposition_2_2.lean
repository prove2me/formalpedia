-- Prove2me | Theorems.Thm_UnivESD_Universality_proposition_2_2
-- name    : UnivESD.Universality.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:33.55392+00:00
-- url     : https://prove2.me/theorems/69944324-b374-49f1-95ae-ef44e2afcca6
-- title:
--   Proposition 2.2 (converging determinant): $\frac1n\log|\det(\frac{A_n}{\sqrt n}-zI)|-\frac1n\log|\det(\frac{B_n}{\sqrt n}-zI)|\to0$
-- statement:
--   Let $x$ and $y$ be complex random variables with zero mean and unit variance, let $X_n$ and $Y_n$ be $n\times n$ random matrices whose entries are i.i.d. copies of $x$ and $y$, let $M_n$ be deterministic $n\times n$ matrices satisfying (1.3), and set $A_n=M_n+X_n$, $B_n=M_n+Y_n$. Then for every fixed $z\in\mathbb C$,
--   $$\frac1n\log\Bigl|\det\Bigl(\frac1{\sqrt n}A_n-zI\Bigr)\Bigr|-\frac1n\log\Bigl|\det\Bigl(\frac1{\sqrt n}B_n-zI\Bigr)\Bigr|\qquad(2.2)$$
--   converges in probability to zero. If furthermore the ESDs of $(\frac1{\sqrt n}M_n-zI)(\frac1{\sqrt n}M_n-zI)^*$ (1.4) converge to a limit for this value of $z$, then (2.2) converges almost surely to zero.
--
--   Together with the replacement principle and the tightness lemma this gives the universality principle; it is the heart of the paper.
--
--   **Formalization Note.** In the paper (2.2) equals $-\infty$ when a determinant vanishes, so its convergence to zero includes that the determinants $\det(\frac1{\sqrt n}A_n-zI)$, $\det(\frac1{\sqrt n}B_n-zI)$ are nonzero with probability $1-o(1)$ (resp. almost surely for all but finitely many $n$). Lean's $\log 0=0$ would assign a real value there instead, so this clause is stated explicitly, in the same form as hypothesis (ii) of Theorem 2.1. The statement holds for every $z$, not almost every $z$. The matrices for different $n$ are corners of one i.i.d. array (relevant for the almost-sure half); the limit in (1.4) is a probability measure.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2035 (PDF 13), Proposition 2.2, (2.2)

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Proposition 2.2 (converging determinant), p. 2035. The paper's (2.2) is `-∞` where a
determinant vanishes, so its convergence includes that the determinants are nonzero with
probability `1 - o(1)` (resp. almost surely for all large `n`); with Lean's `Real.log 0 = 0`
that clause is stated explicitly, in the form of Theorem 2.1 (ii). -/
theorem proposition_2_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs ys : ℕ → ℕ → Ω → ℂ) (hx : IsIIDArray P xs) (hy : IsIIDArray P ys)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : ShiftBound M) (z : ℂ) :
    (TendstoInProbZero P (fun n ω => normLogDet (M n + cornerMatrix xs n ω) z -
        normLogDet (M n + cornerMatrix ys n ω) z) ∧
      Tendsto (fun n => P {ω |
        (invSqrt n • (M n + cornerMatrix xs n ω) - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 ∨
          (invSqrt n • (M n + cornerMatrix ys n ω) - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0})
        atTop (𝓝 0)) ∧
      (ESDConverges (shiftedGram M z) →
        (∀ᵐ ω ∂P, Tendsto (fun n => normLogDet (M n + cornerMatrix xs n ω) z -
          normLogDet (M n + cornerMatrix ys n ω) z) atTop (𝓝 0)) ∧
        ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop,
          (invSqrt n • (M n + cornerMatrix xs n ω) - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0 ∧
            (invSqrt n • (M n + cornerMatrix ys n ω) - z • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0)
    := by sorry

end UnivESD.Universality
