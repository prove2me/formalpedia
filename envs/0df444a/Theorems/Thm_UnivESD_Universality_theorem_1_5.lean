-- Prove2me | Theorems.Thm_UnivESD_Universality_theorem_1_5
-- name    : UnivESD.Universality.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:29.433152+00:00
-- url     : https://prove2.me/theorems/250dec3d-68d5-4d46-8575-e03daf94975e
-- title:
--   Theorem 1.5 (universality principle): $\mu_{\frac1{\sqrt n}A_n}-\mu_{\frac1{\sqrt n}B_n}\to0$ in probability, and almost surely under (1.4)
-- statement:
--   Let $x$ and $y$ be complex random variables with zero mean and unit variance. Let $X_n=(x_{ij})_{1\le i,j\le n}$ and $Y_n=(y_{ij})_{1\le i,j\le n}$ be $n\times n$ random matrices whose entries $x_{ij}$, $y_{ij}$ are i.i.d. copies of $x$ and $y$, respectively. For each $n$ let $M_n$ be a deterministic $n\times n$ matrix satisfying
--   $$\sup_n\frac1{n^2}\|M_n\|_2^2<\infty.\qquad(1.3)$$
--   Let $A_n=M_n+X_n$ and $B_n=M_n+Y_n$. Then $\mu_{\frac1{\sqrt n}A_n}-\mu_{\frac1{\sqrt n}B_n}$ converges in probability to zero: for every continuous compactly supported $f:\mathbb C\to\mathbb R$ and every $\varepsilon>0$,
--   $$\lim_{n\to\infty}\mathbf P\Bigl(\Bigl|\int_{\mathbb C}f\,d\mu_{\frac1{\sqrt n}A_n}-\int_{\mathbb C}f\,d\mu_{\frac1{\sqrt n}B_n}\Bigr|\ge\varepsilon\Bigr)=0.$$
--   If, furthermore, the ESDs of $(\frac1{\sqrt n}M_n-zI)(\frac1{\sqrt n}M_n-zI)^*$ converge to a limit for almost every $z\in\mathbb C$ (1.4), then $\mu_{\frac1{\sqrt n}A_n}-\mu_{\frac1{\sqrt n}B_n}$ converges almost surely to zero: with probability one, the difference of integrals tends to $0$ for every such $f$.
--
--   The limiting ESD of $\frac1{\sqrt n}(M_n+X_n)$ depends only on the mean and variance of the entries, not on their distribution. With $M_n=0$ and Gaussian $y$ this reduces the circular law for arbitrary zero-mean unit-variance entries to the Ginibre computation.
--
--   **Formalization Note.** The $X_n$ (resp. $Y_n$) are the top-left corners of one infinite i.i.d. array on a common probability space; the in-probability statement does not depend on this coupling, the almost-sure one does. No relation between the $x$- and $y$-arrays is assumed. Eigenvalues are counted with algebraic multiplicity; $\|\cdot\|_2$ is the Hilbert–Schmidt norm; the limit in (1.4) is a probability measure (automatic under (1.3)). In the almost-sure statement one null set serves all test functions.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2027 (PDF 5), Theorem 1.5

import Mathlib
import Definitions.Def_UnivESD_Universality_Basic
import Definitions.Def_UnivESD_Universality_Model

open MeasureTheory Filter Topology

namespace UnivESD.Universality

/-- Theorem 1.5 (universality principle), Tao–Vu, Ann. Probab. 38 (2010), p. 2027. -/
theorem theorem_1_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs ys : ℕ → ℕ → Ω → ℂ) (hx : IsIIDArray P xs) (hy : IsIIDArray P ys)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : ShiftBound M) :
    ESDDiffTendstoInProb P (fun n ω => M n + cornerMatrix xs n ω)
        (fun n ω => M n + cornerMatrix ys n ω) ∧
      (Hyp14 M → ESDDiffTendstoAS P (fun n ω => M n + cornerMatrix xs n ω)
        (fun n ω => M n + cornerMatrix ys n ω)) := by sorry

end UnivESD.Universality
