-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_symmetrization_fidelity
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.symmetrization_fidelity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:29:10.510458+00:00
-- url     : https://prove2.me/theorems/ffa942ec-df2c-4dc9-9029-64117ba7b103
-- title:
--   Lemma 2.6.
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   Let $d\ge2$, $n\ge1$, and let $f:[d]^n\to[d]$ be symmetric. For every channel $\Phi$, its finite permutation average $\Phi^P$ and normalized Haar unitary twirl $\Phi^Q$ satisfy
--   $$F_f(\Phi^P)\ge F_f(\Phi),\qquad F_f(\Phi^Q)\ge F_f(\Phi).$$
--   The averages are the fixed maps of (2.26).
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 14, Lemma 2.6.

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

/-- PDF pp.14-15, Lemma 2.6: neither average lowers worst-case fidelity. -/
theorem symmetrization_fidelity (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (f : Word n d → Fin d) (hf : WordSymmetric f)
    (Phi : Superop (Word n d) (Fin d)) (hPhi : IsChannel Phi) :
    functionFidelity (fun _ => True) f Phi ≤ functionFidelity (fun _ => True) f (permutationSymmetrization Phi) ∧
    functionFidelity (fun _ => True) f Phi ≤ functionFidelity (fun _ => True) f (unitarySymmetrization Phi) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
