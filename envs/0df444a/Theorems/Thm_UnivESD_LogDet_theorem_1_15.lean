-- Prove2me | Theorems.Thm_UnivESD_LogDet_theorem_1_15
-- name    : UnivESD.LogDet.theorem_1_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:01.110989+00:00
-- url     : https://prove2.me/theorems/d187f043-7e24-4f4a-90d1-16f34f9aed21
-- title:
--   Theorem 1.15 — ESD convergence ⇔ log-determinant convergence ⇔ regularized log-determinant convergence
-- statement:
--   Let $A_n=M_n+X_n$ be as in Theorem 1.5: $X_n$ is the $n\times n$ corner of an infinite array of i.i.d. copies of a complex random variable $x$ with $\mathbf Ex=0$, $\mathbf E|x|^2=1$, and the deterministic $M_n$ satisfy $\sup_n n^{-2}\|M_n\|_2^2<\infty$. Let $\mu$ be a probability measure on $\mathbb C$ with $\int|z|^2\,d\mu(z)<\infty$. The following are equivalent:
--
--   1. the ESD $\mu_{\frac1{\sqrt n}A_n}$ converges in probability to $\mu$;
--   2. for almost every $z\in\mathbb C$, $\frac1n\log\big|\det(\tfrac1{\sqrt n}A_n-zI)\big|$ converges in probability to $\int_{\mathbb C}\log|w-z|\,d\mu(w)$;
--   3. for almost every $z\in\mathbb C$ there is a deterministic sequence $\varepsilon_n>0$ with $\varepsilon_n\to0$ such that
--   $$\frac1n\log\det\Big(\big(\tfrac1{\sqrt n}A_n-zI\big)\big(\tfrac1{\sqrt n}A_n-zI\big)^*+\varepsilon_nI\Big)$$
--   converges in probability to $2\int_{\mathbb C}\log|w-z|\,d\mu(w)$.
--
--   If, furthermore, for almost every $z$ the ESDs of $(\tfrac1{\sqrt n}M_n-zI)(\tfrac1{\sqrt n}M_n-zI)^*$ converge to a limit (hypothesis (1.4)), then the same three statements with convergence in probability replaced by almost sure convergence are equivalent.
--
--   The theorem reduces the convergence of the non-Hermitian spectral distribution to a family of scalar statements about log-determinants, which are accessible through singular values; it is the criterion by which the circular law and its variants are established.
--
--   **Formalization Note** The matrix in (iii) is printed as "$((\tfrac1{\sqrt n}A_n-zI)+\varepsilon_nI)(\tfrac1{\sqrt n}A_n-zI)^*+\varepsilon_nI$", which is mis-bracketed, and (1.8) on p. 2034 prints $(C+\varepsilon_nI)(C^*+\varepsilon_nI)$; it is read as $CC^*+\varepsilon_nI$ with $C=\tfrac1{\sqrt n}A_n-zI$, the matrix used in §8 ((8.2): $\frac1n\sum\log\sqrt{\sigma_i^2+\varepsilon_n}$) and in the proof of Corollary 1.16. Its determinant is a positive real, and the Lean takes the logarithm of its absolute value. In (ii), Lean's $\log0=0$ replaces the paper's $-\infty$ when the determinant vanishes; for this model the determinant is almost surely nonzero for all large $n$, so the statement is unaffected. The log-potential is a Bochner integral, which is $0$ when not integrable; this happens only on a Lebesgue-null set of $z$ by (8.1), so it is harmless inside "for almost every $z$". The a.s. ESD convergence uses one null set for all test functions; the model couples the $X_n$ as corners of one infinite array.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2032 (PDF 10), Theorem 1.15

import Mathlib
import Definitions.Def_UnivESD_LogDet_Basic
import Definitions.Def_UnivESD_LogDet_Model

open MeasureTheory ProbabilityTheory Filter Topology Matrix

namespace UnivESD.LogDet

/-- Theorem 1.15 (Equivalences for convergence), Tao–Vu, Ann. Probab. 38 (2010), p. 2032.
`A_n = M_n + X_n` as in Theorem 1.5 (i.i.d. array `xs`, condition (1.3)), `μ` a probability
measure on `ℂ` with `∫ |z|² dμ < ∞`. The three statements (i), (ii), (iii) are equivalent, and
under (1.4) their almost-sure versions are equivalent.

Formalization Note: the matrix in (iii) is read as `CC* + ε_n I` with `C = A_n/√n − zI`
(the printed bracketing is a slip; §8 and the proof of Corollary 1.16 use `CC* + ε_n I`).
The sequence `ε` is deterministic (chosen before `ω`). `Real.log ‖det …‖` is the logarithm of
the absolute value of the determinant (with Lean's `Real.log 0 = 0`). -/
theorem theorem_1_15 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (xs : ℕ → ℕ → Ω → ℂ) (hxs : IIDArray P xs)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : HSBound M)
    (μ : Measure ℂ) [IsProbabilityMeasure μ] (hμ : Integrable (fun w : ℂ => ‖w‖ ^ 2) μ) :
    List.TFAE
      [ ESDConvInProb P (normA M xs) μ,
        ∀ᵐ z ∂(volume : Measure ℂ),
          ConvInProb P (fun n ω => (1 / (n : ℝ)) * Real.log ‖(shiftA M xs z n ω).det‖)
            (logPotential μ z),
        ∀ᵐ z ∂(volume : Measure ℂ), ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
          ConvInProb P
            (fun n ω => (1 / (n : ℝ)) * Real.log ‖(shiftA M xs z n ω * (shiftA M xs z n ω)ᴴ
              + ((ε n : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖)
            (2 * logPotential μ z) ] ∧
    (Cond14 M →
      List.TFAE
        [ ESDConvAS P (normA M xs) μ,
          ∀ᵐ z ∂(volume : Measure ℂ),
            ConvAS P (fun n ω => (1 / (n : ℝ)) * Real.log ‖(shiftA M xs z n ω).det‖)
              (logPotential μ z),
          ∀ᵐ z ∂(volume : Measure ℂ), ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
            ConvAS P
              (fun n ω => (1 / (n : ℝ)) * Real.log ‖(shiftA M xs z n ω * (shiftA M xs z n ω)ᴴ
                + ((ε n : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det‖)
              (2 * logPotential μ z) ]) := by sorry

end UnivESD.LogDet
