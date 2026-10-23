-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap50repair_P01_classical_index_degree_independence_parity
-- name    : QAlgorithms.Papers.Independent.Gap50repair.P01.classical_index_degree_independence_parity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:12:55.739048+00:00
-- url     : https://prove2.me/theorems/b3490b5e-1363-41a6-96f2-37583f8a2e0c
-- title:
--   Classical integer Conley–Zehnder index: degree construction, independence and determinant parity
-- statement:
--   Let $n\ge1$ and $T>0$. Let $\gamma:[0,T]\to\operatorname{Sp}(2n,\mathbb R)$ be continuous, with $\gamma(0)=I$ and $\det(\gamma(T)-I)\ne0$. Put $\gamma_u(s)=\gamma(Ts)$ and let $\rho$ be the source's spectral rotation map (18). An admissible extension $e:[0,2]\to\operatorname{Sp}(2n,\mathbb R)$ agrees with $\gamma_u$ on $[0,1]$, avoids eigenvalue $1$ on $[1,2]$, and ends at $W^+=-I$ or $W^-=\operatorname{diag}(2,-1,\ldots,-1,1/2,-1,\ldots,-1)$. Such an extension exists. For every such extension,
--
--   $$\mu_{\rm CZ}(\gamma)=\deg(\rho^2\circ e)\in\mathbb Z,\qquad (-1)^{n-\mu_{\rm CZ}(\gamma)}=\operatorname{sign}\det(I-\gamma(T)).$$
--
--   The degree is oriented winding: its continuous angle lift starts at zero and ends at this integer, and a positive full turn has degree $+1$. Thus the value is independent of the extension. Intermediate degeneracies of $\gamma$ are allowed. This supplies the classical integer index and its endpoint parity.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, PDF p. 1, Classical integer Conley–Zehnder index: degree construction, independence and determinant parity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)

open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Definitions 32–33, extension existence, Lemma 34 and Proposition 35(7),
PDF pp.35–36,40: genuine integer winding, independence, and parity. -/
theorem classical_index_degree_independence_parity {n : ℕ} (hn : 1 ≤ n)
    (p : ℝ → GroupedRealMatrix n) (T : ℝ) (hT : 0 < T) (hp : IsAdmissible p T) :
    (∃ e, IsExtension (unitPath p T) e) ∧
    (∀ e, IsExtension (unitPath p T) e →
      IsWindingLift (fun t => spectralRotation (e t)^2) 2 (conleyZehnder p T) ∧
      conleyZehnder p T = winding (fun t => spectralRotation (e t)^2) 2) ∧
    (-1 : ℝ)^((n : ℤ)-conleyZehnder p T) = Real.sign ((1-p T).det) := by sorry

end QAlgorithms.Papers.Independent.Gap50repair.P01

end
