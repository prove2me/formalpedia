-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P41_symplectic_bases_pairing
-- name    : QAlgorithms.Papers.Independent.Claimed50.P41.symplectic_bases_pairing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:56:11.565199+00:00
-- url     : https://prove2.me/theorems/f42eabe5-4433-4be9-bb27-63f35929b764
-- title:
--   §III (3.3)–(3.5): symplectic bases and invariant pairing
-- statement:
--   Let $n\ge1$ and let $V$ be a real vector space of dimension $2n$, with a nondegenerate alternating bilinear form $B$. For a subspace $W$, put $k=\dim W$, let $r(W)$ be the rank of $B|_{W\times W}$, and put $W^\perp=\{x:B(w,x)=0\text{ for all }w\in W\}$. Write $\beta$ for the grouped canonical matrix. Explicitly $\beta=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$.
--
--   $$
--   [B]_{\mathcal B}=\beta,\qquad [B]_{\mathcal C}=\bigoplus_{r=1}^n\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad (Sx)^T\beta(Sy)=x^T\beta y.
--   $$
--
--   Both bases exist; the paired basis uses an explicit coordinate permutation. The final equality holds for every symplectic matrix and all coordinate vectors. It identifies the invariant alternating pairing rather than a Euclidean inner product.
-- source:
--   The Real Symplectic Groups in Quantum Mechanics and Optics, arXiv:quant-ph/9509002v3, PDF p. 7, §III (3.3)–(3.5): symplectic bases and invariant pairing

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P41

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma thermalCovariance)

namespace QAlgorithms.Papers.Independent.Claimed50.P41

/-- PDF pp.7–8, (3.3)–(3.5): grouped and paired symplectic bases exist;
the pairing is preserved, with no Euclidean orthogonality claim. -/
theorem symplectic_bases_pairing (n : ℕ) (hn : 0 < n)
    (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2 * n) (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    (∃ b : Module.Basis (Phase n) ℝ V, ∀ i j, B (b i) (b j) = sigma n i j) ∧
    (∃ b : Module.Basis (Fin n × Bool) ℝ V, ∀ i j,
      B (b i) (b j) = sigma n
        (if i.2 then Sum.inr i.1 else Sum.inl i.1)
        (if j.2 then Sum.inr j.1 else Sum.inl j.1)) ∧
    (∀ S : Matrix (Phase n) (Phase n) ℝ, PreservesCanonicalForm S →
      ∀ x y : Phase n → ℝ,
        (∑ i, ∑ j, (Matrix.mulVec (S) x) i * sigma n i j * (Matrix.mulVec (S) y) j) =
          ∑ i, ∑ j, x i * sigma n i j * y j) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P41

end
