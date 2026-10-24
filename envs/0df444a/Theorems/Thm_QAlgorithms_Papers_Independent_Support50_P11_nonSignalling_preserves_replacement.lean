-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_nonSignalling_preserves_replacement
-- name    : QAlgorithms.Papers.Independent.Support50.P11.nonSignalling_preserves_replacement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:18:30.570499+00:00
-- url     : https://prove2.me/theorems/4965d17a-c66b-469d-9a7c-8f9c091a34ae
-- title:
--   Appendix B: non-signalling supermaps preserve replacement channels
-- statement:
--   Let $A',B$ be positive finite systems, $\sigma$ a density matrix on $B$, and $\mathcal R:A'\to B$ the replacement channel $\mathcal R(X)=\operatorname{Tr}(X)\sigma$. Let $K\ge1$ and let $\mathcal Z$ be any actual forward-assisted code of size $K$ non-signalling also from Alice to Bob. Then there exists a density matrix $\tau$ on the receiver's $K$-dimensional output such that
--   $$\mathcal Z[\mathcal R](X)=\operatorname{Tr}(X)\tau\qquad\text{for every operator }X.$$
--   Thus the deterministic supermap represented by any such bipartite code preserves replacement channels. Both replacement states are normalized; single-input replacement terminology is distinguished from bipartite non-signalling.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 14, Appendix B: non-signalling supermaps preserve replacement channels

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.14, Appendix B: a non-signalling deterministic supermap sends any
normalized replacer channel to another normalized replacer channel. -/
theorem nonSignalling_preserves_replacement
    {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]
    (K : ℕ) (hK : 0 < K) (sigma : Matrix O O ℂ) (hsigma : IsDensityMatrix sigma)
    (Z : Superop (Fin K × O) (I × Fin K)) (hZ : IsForwardCode K .NS Z) :
    ∃ tau : Matrix (Fin K) (Fin K) ℂ, IsDensityMatrix tau ∧
      ∀ X, link K (replacer (A := I) sigma) Z X = X.trace • tau := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
