-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P01_relative_entropy_dominated_limit
-- name    : QAlgorithms.Papers.Independent.Frontier18.P01.relative_entropy_dominated_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:00:32.587668+00:00
-- url     : https://prove2.me/theorems/8cee5b37-a466-4d80-8f2e-0b74ec47cad5
-- title:
--   Appendix Lemma 7: relative-entropy continuity under domination
-- statement:
--   All Hilbert spaces are complex and separable, with completed Hilbert tensor products. States are positive trace-class operators of trace one, and channels are completely positive and trace preserving. Write $H$ for entropy and $D$ for relative entropy, using natural logarithms; $I(\rho,\Phi)$ is the relative entropy of the channel-applied purification against the product of its marginals. Let $A_n,A_0,B$ be arbitrary positive trace-class operators. Assume $A_n\to A_0$ in trace norm and $A_n\le A_0$ for all $n$. Then
--
--   $$D(A_n\Vert B)\longrightarrow D(A_0\Vert B)\quad\text{in }[0,+\infty].$$
--
--   Normalization, monotonicity of the sequence, and finite relative entropy are not required. In particular, $A_0=0$ forces every $A_n=0$, and the limiting value is $\operatorname{Tr}B$.
-- source:
--   Mutual and coherent informations for infinite-dimensional quantum channels, arXiv:1004.2495v2, PDF p. 25, Appendix Lemma 7: relative-entropy continuity under domination

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01

noncomputable section

open Filter

open scoped ENNReal

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Frontier18.P01

variable {I J K L E R : Type}

/-- Appendix Lemma 7, PDF p.25. Arbitrary positive trace class, not states;
no monotonicity of A_n or entropy finiteness, and the limit may be infinity. -/
theorem relative_entropy_dominated_limit [Countable I] (A : ℕ → Matrix I I ℂ) (A0 B : Matrix I I ℂ)
    (hA : ∀ n, IsTraceClass (A n) ∧ IsPositive (A n))
    (hA0 : IsTraceClass A0) (hpos0 : IsPositive A0)
    (hB : IsTraceClass B) (hposB : IsPositive B)
    (hlim : Tendsto (fun n => traceSize (A n - A0)) atTop (nhds 0))
    (hdom : ∀ n, TraceOperatorLE (A n) A0) :
    Tendsto (fun n => generalizedRelativeEntropy (A n) B) atTop
      (nhds (generalizedRelativeEntropy A0 B)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P01

end
