-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_no_perfect_majority
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.no_perfect_majority
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:27:33.297097+00:00
-- url     : https://prove2.me/theorems/5eccaf5d-ce92-4355-9c12-ff9a71863227
-- title:
--   §2.4: impossibility of perfect quantum majority
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   Let $n\ge3$ be odd. Every channel $\Phi$ fails on some word and basis:
--   $$\forall\Phi\ \exists x,U:\quad \Phi(\rho_x^U)\ne U|\operatorname{MAJ}_n(x)\rangle\langle\operatorname{MAJ}_n(x)|U^\dagger.$$
--   This is an obstruction to exact ideal output equality for every input.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 13, §2.4: impossibility of perfect quantum majority

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

/-- PDF pp.13-14, section 2.4: every fixed CPTP map fails exact ideal equality
on some input and common basis, for every odd n>=3. -/
theorem no_perfect_majority (n : ℕ) (hn : 3 ≤ n) (hodd : Odd n)
    (Phi : Superop (Word n 2) (Fin 2)) (hPhi : IsChannel Phi) :
    ∃ x : Word n 2, ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      Phi (encodedInput U.val x) ≠ targetDensity U.val (majority n x) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
