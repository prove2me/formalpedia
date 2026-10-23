-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P14_splitFockStatistics
-- name    : QAlgorithms.Papers.Independent.Frontier18.P14.splitFockStatistics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:06:10.148972+00:00
-- url     : https://prove2.me/theorems/825faf43-6de1-428d-8375-4fd2a461f4ac
-- title:
--   Fock splitting and normalized binomial counting law
-- statement:
--   Let $B$ be a lossless two-mode beam matrix and let $n\in\mathbb N$. With input $|n,0\rangle$, the normalized output is
--
--   $$V_B|n,0\rangle=\sum_{k=0}^n\sqrt{\binom nk}B_{11}^kB_{21}^{n-k}|k,n-k\rangle.$$
--
--   Writing $p=|B_{11}|^2$, ideal joint photon counting gives
--
--   $$\Pr(n_1,n_2)=\begin{cases}\binom n{n_1}p^{n_1}(1-p)^{n_2},&n_1+n_2=n,\\0,&n_1+n_2\ne n.\end{cases}$$
--
--   The Born weights are summable and sum to one. This includes vacuum input and deterministic endpoints $p=0,1$. It makes precise the statistical distribution of incident photons between the two output modes.
-- source:
--   Quantum Physics of Simple Optical Instruments, arXiv:quant-ph/0305007v2, PDF p. 21, §4.3: splitting a Fock input and its binomial counting law

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P14

open QAlgorithms.Papers.Independent.Dependency50.P34 (fockKet)

/-- PDF pp.21–22, (4.20)–(4.22): Fock splitting and its normalized joint
Born law. The printed (4.22) omits a sum and leaves k unbound; the guarded law
below is the equivalent sum of delta terms from (4.20). Includes n=0 and zero/one
transmissivity without negative exponents or unguarded natural subtraction. -/
theorem splitFockStatistics (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (n : ℕ) :
    passiveApply B (fockKet n 0) =
      ∑ k ∈ Finset.range (n + 1),
        ((Real.sqrt (n.choose k : ℝ) : ℂ) * B 0 0 ^ k * B 1 0 ^ (n - k)) •
          fockKet k (n - k) ∧
    ‖passiveApply B (fockKet n 0)‖ = 1 ∧
    (∀ n1 n2 : ℕ, Complex.normSq (passiveApply B (fockKet n 0) (n1, n2)) =
      if n1 + n2 = n then
        (n.choose n1 : ℝ) * Complex.normSq (B 0 0) ^ n1 *
          (1 - Complex.normSq (B 0 0)) ^ n2 else 0) ∧
    Summable (fun mn : ℕ × ℕ => Complex.normSq (passiveApply B (fockKet n 0) mn)) ∧
    (∑' mn : ℕ × ℕ, Complex.normSq (passiveApply B (fockKet n 0) mn)) = 1 := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P14

end
