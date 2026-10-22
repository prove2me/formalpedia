-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_seed_diagram_formula
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.seed_diagram_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:52:12.530293+00:00
-- url     : https://prove2.me/theorems/e9bfe30e-426d-4a1e-872c-41997e137794
-- title:
--   Lemma B.5.
-- statement:
--   For $n\ge1$, write $\lambda=(n-k,k)$, $0\le k\le\lfloor n/2\rfloor$, $\ell_\lambda=n-2k$, $m_\lambda=\ell_\lambda+1$ and $d_\lambda=\binom nk-\binom n{k-1}$, where $\binom n{-1}=0$. The source vectors $|\lambda,w,i\rangle$ are constructed from the Dicke vector $|s_{\ell_\lambda}(w)\rangle$ followed by $k$ ordered normalized singlets. The same fixed real permutation coefficients are used for every $w$, and are orthonormalized and spanning only at $w=0$. All labels have their actual dependent ranges. Let $Q_\lambda(M)=\det(M)^kT^{n-2k}(M)$, where $T^\ell$ is the explicit normalized-monomial matrix of (C.9). Let $\Gamma$ be the source Schur transform followed by shape measurement and multiplicity trace, and let $\Gamma'$ append $I_{d_\lambda}/d_\lambda$ in each measured sector and apply inverse Schur. Write $\Theta$ for permutation averaging.
--
--   Let $\gamma$ be the source diagram for $\lambda,\pi$, with its closed-component count $L$ and oriented contraction sign $\sigma\in\{1,-1\}$. Then
--   $$\langle\lambda,w,0|P(\pi)|\mu,v,0\rangle=\begin{cases}\sigma 2^{L-\lambda_2},&\lambda=\mu,\ w=v,\ \gamma\text{ proper},\\0,&\text{otherwise}.\end{cases}$$
--   The sign is independently constructed from binary labels respecting wires, opposite singlet endpoints and ordered singlet amplitudes; the exponent is an integer.
--
--   This identifies the source-constructed Schur coordinates and their operational use in the majority algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 53, Lemma B.5.

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

/-- PDF pp.53-54, Lemma B.5: the graph coefficient and full heterogeneous
seed identity. The exponent loops-k is in Z, preserving negative powers. -/
theorem seed_diagram_formula (n : ℕ) (hn : 1 ≤ n)
    (k l : TwoRowShape n) (p : Equiv.Perm (Fin n))
    (w : Fin (degree n k+1)) (v : Fin (degree n l+1)) :
    (diagramSign k p = 1 ∨ diagramSign k p = -1) ∧
    inner ℂ (schurSeed n k w)
      (WithLp.toLp 2 ((wordPermutationMatrix n 2 p).mulVec (schurSeed n l v))) =
      if k = l ∧ w.val = v.val then
        if ProperMatching k k p then
          ((diagramSign k p * (2:ℝ)^((diagramLoops k p : ℤ)-(k.val:ℤ))) : ℂ)
        else 0
      else 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
