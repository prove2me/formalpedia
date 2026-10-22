-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_fidelity_linear_program
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.fidelity_linear_program
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:43:07.092537+00:00
-- url     : https://prove2.me/theorems/a6e2b58a-7508-4ea3-ad3e-f4082febce03
-- title:
--   Theorem 4.7.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For positive odd $n$ and symmetric equivariant Boolean $f$, put $\bar f(h)=f(0^{n-h}1^h)$ and
--   $$p_k(h)=\frac{\binom nk-\binom n{k-1}}{\binom nh},\quad a_k(h)=\frac{n-h-k-\bar f(h)(n-2h)}{n-2k},\quad b_k(h)=\frac{h-k+1+\bar f(h)(n-2h)}{n-2k+2}.$$
--   The maximum of $c$ under $0\le t_k\le1$ and $c\le\sum_{k=0}^h p_k(h)[t_ka_k(h)+(1-t_k)b_k(h)]$ for each $0\le h\le\lfloor n/2\rfloor$ is attained and equals $F_f$. Every maximizing parameter vector gives an optimal $A_t$. There are $\lfloor n/2\rfloor+2$ real variables and $3\lfloor n/2\rfloor+3$ inequalities.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 31, Theorem 4.7.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.31-32, Theorem 4.7: the explicit LP has an attained optimum equal
to channel optimal fidelity; EVERY optimizer transfers to Algorithm 2. The
variable and inequality counts are built into FunctionLPFeasible. -/
theorem fidelity_linear_program (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n)
    (alpha : RealSchurCoefficients n) (ha : LawfulCoefficients alpha)
    (f : Word n 2 → Fin 2) (hf : WordSymmetric f) (he : Equivariant f) :
    (∃ t : TwoRowShape n → ℝ, FunctionLPFeasible f (optimalFunctionFidelity (fun _ => True) f) t) ∧
    (∀ c t, FunctionLPFeasible f c t → c ≤ optimalFunctionFidelity (fun _ => True) f) ∧
    (∀ c t, FunctionLPFeasible f c t → c = optimalFunctionFidelity (fun _ => True) f →
      IsFunctionOptimal (fun _ => True) f (template alpha t)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
