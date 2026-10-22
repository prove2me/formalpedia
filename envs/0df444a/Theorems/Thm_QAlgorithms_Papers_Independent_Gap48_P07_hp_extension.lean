-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P07_hp_extension
-- name    : QAlgorithms.Papers.Independent.Gap48.P07.hp_extension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:12:33.974057+00:00
-- url     : https://prove2.me/theorems/1709d419-14ef-4bd4-8201-5f9de1cbf0f8
-- title:
--   §2.2, unnumbered regularized HP extension
-- statement:
--   Let $-A$ generate a bounded strongly continuous semigroup $T$ on a complex Banach space $X$, and fix its elementary integral calculus $\rho_T$. A holomorphic symbol $f$ on $\mathbb C_+=\{\Re z>0\}$ is regularizable if there is $e\in A_+^1$ with $ef\in A_+^1$ and $\rho_T(e)$ injective. For every such regularizer,
--   $$\operatorname{graph}f(A)=\{(x,y):\rho_T(ef)x=\rho_T(e)y\},\qquad \operatorname{dom}f(A)=\{x:\rho_T(ef)x\in\operatorname{ran}\rho_T(e)\}.$$
--   This graph is independent of $e$ and is a closed complex linear operator. The regularizable symbols form a unital complex algebra. This is the canonical extended Hille–Phillips calculus for this same semigroup.
--
--   Throughout, $\mathbb R_+=[0,\infty)$, $\mathbb C_+=\{\Re z>0\}$, and $A_+^1$ is the finite complex-measure Laplace image. For semigroup results, $C_t(A)x=t^{-1}\int_0^tT(s)x\,ds$ and all limits of rates are as $t\to+\infty$. A Bernstein representation $g\sim(a,b,\mu)$ means $g(z)=a+bz+\int_{(0,\infty)}(1-e^{-sz})\,\mu(ds)$ with $a,b\ge0$ and $\int s/(1+s)\,\mu(ds)<\infty$. Where used, $r[g](t)=a/2+b/t+\int\min(s/t,1)\,\mu(ds)$.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, PDF p. 5, §2.2, unnumbered regularized HP extension

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07

noncomputable section

open Set Filter MeasureTheory

open scoped Topology NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P07

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore graphPower)

open QAlgorithms.Papers.Independent.Renew46.P11
  (LaplaceImage Bernstein CompletelyMonotone SpecialBernstein StieltjesClass PositiveReal)

attribute [local instance] Classical.propDecidable

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- PDF p.5: regularizer-independent closed extension and its exact natural
 domain; the regularizable symbols form a unital algebra. -/
theorem hp_extension (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) :
    UnitalSubalgebraSet {f : ℂ → ℂ | HPRegularizable T f} ∧
    ∀ f : ℂ → ℂ, HPRegularizable T f → BanachClosedOperator (hpGraph T f) ∧
      ∀ e : ℂ → ℂ, HPRegularizer T f e →
        hpGraph T f = {p | hpEval T (e * f) p.1 = hpEval T e p.2} ∧
        graphDomain (hpGraph T f) = {x | hpEval T (e * f) x ∈ Set.range (hpEval T e)} := by sorry

end QAlgorithms.Papers.Independent.Gap48.P07

end
