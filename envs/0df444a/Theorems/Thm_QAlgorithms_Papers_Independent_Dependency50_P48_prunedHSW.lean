-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_prunedHSW
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.prunedHSW
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:44:18.382998+00:00
-- url     : https://prove2.me/theorems/5fd0c5e4-406d-4a1d-8c66-2ba03c6faeaa
-- title:
--   HSW coding under the normalized pruned input distribution
-- statement:
--   Fix a finite nonempty alphabet $X$, a probability distribution $p$ on $X$, and normalized density matrices $\omega_x$ on a finite nonempty register $Q$. Let $I=H(\sum_xp_x\omega_x)-\sum_xp_xH(\omega_x)$, in bits. For $\delta>0$, let $T_{p,\delta}^n$ consist of words whose letter counts differ from $np_x$ by at most $n\delta$ for every letter, and let $p'$ be $p^{\otimes n}$ conditioned on this set.
--
--   There exist constants $c,c'>0$, fixed for the ensemble before $\delta$ and $n$, such that for every $\delta>0$ and every sufficiently large positive $n$, the typical-set mass is positive and at least $1-\epsilon_n$, where $\epsilon_n=2^{-nc'\delta^2}$. Set
--
--   $$
--   u_n=\max\{1,\lfloor 2^{n[I-2(c+c'\delta)\delta]}\rfloor\}.$$
--
--   Choose $
--   u_n$ codewords independently according to $p'$. For each codebook there is a genuine $
--   u_n$-outcome decoding POVM on $Q^{\otimes n}$, with
--
--   $$\mathbb E_{\mathrm{codebook}}\!\left[\frac1{
--   u_n}\sum_{s=1}^{
--   u_n}\operatorname{Tr}(\omega_{U_s}(I-Y_s))\right]\le10\epsilon_n.$$
--
--   The blocklength threshold may depend on $\delta$. For negative nominal rate the one-message convention gives zero error. This is the modified random-coding statement needed for the pruned distribution.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 17, Appendix B, unnumbered theorem

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Appendix B, PDF p.17 (setup pp.6,16): IID pruned codebooks have genuine
POVM decoders with expected error <=10*2^(-n*cprime*delta^2).
Constants precede delta and n. A support-completed PGM cannot worsen error. -/
theorem prunedHSW [Nonempty X] [Nonempty Q]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hnorm : ∑ x, p x = 1)
    (omega : X → Matrix Q Q ℂ) (homega : ∀ x, IsDensityMatrix (omega x)) :
    ∃ c : ℝ, 0 < c ∧ ∃ cprime : ℝ, 0 < cprime ∧
      ∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
        let eps := Real.rpow 2 (-(n : ℝ) * cprime * delta ^ 2)
        let nu := hswSize (holevoInformation p omega) c cprime delta n
        0 < typicalMass p delta n ∧ 1 - eps ≤ typicalMass p delta n ∧
        ∃ Y : (Fin nu → Fin n → X) → Fin nu → Matrix (Fin n → Q) (Fin n → Q) ℂ,
          (∀ book, IsPOVM (Y book)) ∧ hswExpectedError p omega delta n nu Y ≤ 10 * eps := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
