-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_image_additivity_entropy_additivity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.image_additivity_entropy_additivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:24:30.118458+00:00
-- url     : https://prove2.me/theorems/f12a9454-97aa-4b10-8d9b-44394952bfe0
-- title:
--   Image additivity implies minimum Rényi additivity
-- statement:
--   Let $T_i:M_{d_i}(\mathbb C)\to M_{n_i}(\mathbb C)$ be quantum channels in positive finite dimensions. Suppose their physical tensor image is the convex hull of products of their individual images. For every real $p\ge1$,
--   $$H_{\min}^{(p)}(T_1\otimes T_2)=H_{\min}^{(p)}(T_1)+H_{\min}^{(p)}(T_2).$$
--   Here $H_{\min}^{(p)}$ is the minimum output Rényi entropy in bits; at $p=1$ it uses the von Neumann entropy with the minus sign required by the Rényi limit.
--
--   This is the implication meant by the source's statement that image additivity is stronger than entropy additivity.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 10, §6, unnumbered: image additivity implies minimum Rényi entropy additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- §6, unnumbered implication, PDF p.10: image additivity implies equation (11) for
every real p≥1. Source correction: p.7 prints +sum x log x at p=1;
changed to -sum x log_2 x because the source specifies the p-to-1 limit.
The unspecified logarithm base is fixed to two, a common positive rescaling. -/
theorem image_additivity_entropy_additivity {d1 d2 n1 n2 : ℕ}
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (T : Superop (Fin d1) (Fin n1)) (S : Superop (Fin d2) (Fin n2))
    (hT : IsChannel T) (hS : IsChannel S) (hImage : IsImageAdditive T S)
    (p : ℝ) (hp : 1 ≤ p) :
    minimumOutputRenyiEntropy p (tensorOnFunctions T S) =
      minimumOutputRenyiEntropy p T + minimumOutputRenyiEntropy p S := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
