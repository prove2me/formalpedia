-- Prove2me | Theorems.Thm_QAlgorithms_Arunachalam_fourier_comp_matrix
-- name    : QAlgorithms.Arunachalam.fourier_comp_matrix
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:55:17.289759+00:00
-- url     : https://prove2.me/theorems/071efd13-5d38-4cbe-9867-69911964e33a
-- title:
--   Fourier coefficients of f composed with a linear map over F2
-- statement:
--   Let $f:\{0,1\}^m\to\mathbb R$ and let $M\in\mathbb F_2^{m\times k}$. The Fourier coefficient of $g:\{0,1\}^n\to\mathbb R$ at $S\subseteq[n]$ (identified with its indicator vector) is $\hat g(S)=\mathbb E_{x}[g(x)(-1)^{S\cdot x}]$ with $x$ uniform on $\{0,1\}^n$, and $(f\circ M)(z)=f(Mz)$ with arithmetic over $\mathbb F_2$. Then for every $Q\subseteq[k]$,
--
--   $$
--   \widehat{f\circ M}(Q)=\sum_{S\in\{0,1\}^m:\ M^{\mathsf T}S=Q}\hat f(S).
--   $$
--
--   This identity is used to compute the spectrum of Gram matrices of ensembles indexed by codewords of a linear code.
--
--   **Formalization Note** Bit strings are vectors over `ZMod 2`, so $Mz$ and $M^{\mathsf T}S$ are matrix-vector products over $\mathbb F_2$.
-- source:
--   Srinivasan Arunachalam, Quantum Algorithms and Learning Theory — Part II, 2018 thesis, ILLC DS-2018-08, PDF p. 161, Claim 7.3.5. https://ir.cwi.nl/pub/27536/Thesis_S_Arunachalam

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
set_option autoImplicit false

namespace QAlgorithms.Arunachalam


/-- Arunachalam p.161, Claim 7.3.5: for `f : {0,1}^m → ℝ` and `M ∈ F₂^{m×k}`, the Fourier
coefficients of `f ∘ M` (`(f ∘ M)(z) = f(Mz)` over `F₂`) are
`\widehat{f∘M}(Q) = ∑_{S ∈ {0,1}^m : Mᵀ S = Q} \hat f(S)` for every `Q ⊆ [k]` (identified with
its indicator vector). -/
theorem fourier_comp_matrix {m k : ℕ} (f : (Fin m → ZMod 2) → ℝ)
    (M : Matrix (Fin m) (Fin k) (ZMod 2)) (Q : Fin k → ZMod 2) :
    boolFourier (fun z => f (M.mulVec z)) Q =
      ∑ S ∈ Finset.univ.filter (fun S : Fin m → ZMod 2 => M.transpose.mulVec S = Q),
        boolFourier f S := by
  sorry





end QAlgorithms.Arunachalam
