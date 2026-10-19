-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_hybrid_entropy_formula
-- name    : QAlgorithms.Papers.Independent.Information100.P56.hybrid_entropy_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:23:49.509705+00:00
-- url     : https://prove2.me/theorems/025faa46-4549-41bf-a607-7a48bfaca621
-- title:
--   Section VI C, Eqs.(51)–(52): hybrid binary entropy formula
-- statement:
--   Let the input alphabet be finite and nonempty, and let Bob and Eve have nonzero finite-dimensional output spaces. Each channel output is a positive semidefinite matrix of trace one. Entropies and information rates use natural logarithms, with $0\log0=0$. In the hybrid binary channel, Bob has the binary symmetric channel of crossover $q$, while Eve receives $|\psi_b\rangle=\sqrt{q^{\prime}}|0\rangle+(-1)^b\sqrt{1-q^{\prime}}|1\rangle$. Here $q,q^{\prime}\in[0,1]$, and $x$ is the probability of input symbol $1$. Write $h$ for natural binary entropy. Bob's average output is $\operatorname{Bern}(x(1-q)+(1-x)q)$, and Eve's average state has diagonal $q^{\prime},1-q^{\prime}$ and off-diagonal $(1-2x)\sqrt{q^{\prime}(1-q^{\prime})}$. Its two eigenvalues are $(1\pm\sqrt{1-16q^{\prime}(1-q^{\prime})x(1-x)})/2$. Consequently
--
--   $$\Delta(x;q,q^{\prime})=h(x(1-q)+(1-x)q)-h\!\left(\frac{1-\sqrt{1-16q^{\prime}(1-q^{\prime})x(1-x)}}2\right).$$
--
--   This function is unchanged by $x\mapsto1-x$. The formula includes all parameter endpoints.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 14, Section VI C, Eqs.(51)–(52): hybrid binary entropy formula

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section VI C, pp.14–15, Eqs.(51)–(52): exact hybrid average and entropy formula,
symmetric in x and 1-x. Parameters at zero and one are included. -/
theorem hybrid_entropy_formula (q qprime x : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hqp : qprime ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    average (hybridBob q) (bernoulli x) =
      Matrix.diagonal (fun b => (bernoulli (binaryConvolution x q) b : ℂ)) ∧
    average (hybridEve qprime) (bernoulli x) =
      (fun j k : Bool => if j = k then (if j then (1 - qprime : ℂ) else (qprime : ℂ))
        else (((1 - 2 * x) * Real.sqrt (qprime * (1 - qprime)) : ℝ) : ℂ)) ∧
    (∀ y : ℂ,
      let s := Real.sqrt (1 - 16 * qprime * (1 - qprime) * x * (1 - x))
      Matrix.det (y • (1 : Matrix Bool Bool ℂ) - average (hybridEve qprime) (bernoulli x)) =
        (y - (((1 - s) / 2 : ℝ) : ℂ)) * (y - (((1 + s) / 2 : ℝ) : ℂ))) ∧
    binaryDelta (hybridBob q) (hybridEve qprime) x = hybridFormula q qprime x ∧
    hybridFormula q qprime (1 - x) = hybridFormula q qprime x := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
