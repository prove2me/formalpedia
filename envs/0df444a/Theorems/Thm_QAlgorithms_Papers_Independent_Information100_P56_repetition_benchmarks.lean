-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_repetition_benchmarks
-- name    : QAlgorithms.Papers.Independent.Information100.P56.repetition_benchmarks
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:26:40.901412+00:00
-- url     : https://prove2.me/theorems/379b6897-50cb-4d51-aea4-9c9ce6cf00b6
-- title:
--   Section VII A, Eqs.(66)–(73): three repetition benchmarks
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. In the hybrid binary channel, Bob has the binary symmetric channel of crossover $q$, while Eve receives $|\psi_b\rangle=\sqrt{q^{\prime}}|0\rangle+(-1)^b\sqrt{1-q^{\prime}}|1\rangle$. Here $q,q^{\prime}\in[0,1]$, and $x$ is the probability of input symbol $1$. Write $h$ for natural binary entropy. Specialize to $q=q^{\prime}=p\in(0,1/2)$ and $n\ge1$. Let $R_n^{\rm rep,0}$ optimize uniform logical repetition over $\lambda\in[0,1/2]$; let $R_n^{\rm rep,log}$ also optimize a logical flip $\mu\in[0,1/2]$; and let $R_n^{\rm rep}$ optimize the full single-use private information of the binary repetition-preprocessed channel over $\lambda$, divided by $n$. If
--
--   $$F_\lambda(x)=\Delta_n\!\left(x\operatorname{Bern}(1-\lambda)^{\otimes n}+(1-x)\operatorname{Bern}(\lambda)^{\otimes n}\right),$$
--
--   then
--
--   $$R_n^{\rm rep}=\frac1n\max_{\lambda\in[0,1/2],\ x\in[0,1]}[F_\lambda(x)-(F_\lambda)_{\rm vex}(x)]\ge R_n^{\rm rep,log}\ge R_n^{\rm rep,0}.$$
--
--   All maxima are attained and all three rates are achievable. The full logical auxiliary is unrestricted; no assertion that its optimum has uniform prior or belongs to the pair family is made.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 17, Section VII A, Eqs.(66)–(73): three repetition benchmarks

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VII A, pp.17–18, Eqs.(66)–(73): nested repetition benchmarks and the
full convex-envelope expression, all bounded by the unrestricted n-use rate. -/
theorem repetition_benchmarks (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 0 < p ∧ p < 1 / 2) :
    repetitionZero n p ≤ repetitionLogical n p ∧
    repetitionLogical n p ≤ repetitionFull n p ∧
    repetitionFull n p ≤ blockPrivate n (hybridBob p) (hybridEve p) / n ∧
    repetitionFull n p = sSup {r : ℝ |
      ∃ lambda ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ x ∈ Set.Icc (0 : ℝ) 1,
        let F := fun y => hybridBlockDelta n p p
          (fun z => y * physicalNoise n (1 - lambda) z + (1 - y) * physicalNoise n lambda z)
        r = (F x - convexEnvelope F x) / n} ∧
    (∃ lambda ∈ Set.Icc (0 : ℝ) (1 / 2),
      repetitionZero n p = repetitionRate n p p lambda 0) ∧
    (∃ lambda ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ mu ∈ Set.Icc (0 : ℝ) (1 / 2),
      repetitionLogical n p = repetitionRate n p p lambda mu) ∧
    (∃ lambda ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ x ∈ Set.Icc (0 : ℝ) 1,
      let F := fun y => hybridBlockDelta n p p
        (fun z => y * physicalNoise n (1 - lambda) z + (1 - y) * physicalNoise n lambda z)
      repetitionFull n p = (F x - convexEnvelope F x) / n) ∧
    AchievableRate (hybridBob p) (hybridEve p) (repetitionZero n p) ∧
    AchievableRate (hybridBob p) (hybridEve p) (repetitionLogical n p) ∧
    AchievableRate (hybridBob p) (hybridEve p) (repetitionFull n p) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
