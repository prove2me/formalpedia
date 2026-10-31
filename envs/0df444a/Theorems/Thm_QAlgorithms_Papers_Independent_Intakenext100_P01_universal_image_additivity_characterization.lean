-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_universal_image_additivity_characterization
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.universal_image_additivity_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:16:27.575373+00:00
-- url     : https://prove2.me/theorems/0733f8e8-5ff2-4152-9257-d63217642716
-- title:
--   Five equivalent descriptions of universal image additivity
-- statement:
--   Let $d,n\ge1$ and let $T:M_d(\mathbb C)\to M_n(\mathbb C)$ be a quantum channel. The following five assertions are equivalent:
--
--   1. For every channel $S$ in every pair of positive finite dimensions, the pair $(T,S)$ is image additive.
--   2. $T$ and the identity channel on $M_d(\mathbb C)$ are image additive.
--   3. There is an entanglement-breaking channel $S:M_d(\mathbb C)\to M_d(\mathbb C)$ with $T=T\circ S$.
--   4. There is an essentially classical-quantum channel $S:M_d(\mathbb C)\to M_d(\mathbb C)$ with $T=T\circ S$.
--   5. $T$ is essentially classical-quantum.
--
--   Image additivity means
--   $$\operatorname{Im}(T\otimes S)=\operatorname{conv}\{A\otimes B:A\in\operatorname{Im}T,\ B\in\operatorname{Im}S\}.$$
--   Essentially classical-quantum means a measure-and-prepare representation with every POVM effect of spectral norm one. All channel equalities hold on every operator.
--
--   This is the paper's second main characterization.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 10, Theorem 6.2; second informal theorem on p.2

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

/-- Theorem 6.2, PDF pp.10–11 (informal seed p.2): all five assertions, linked by four
iff statements. The precomposing S in (c),(d) acts on the input algebra; equality is on all operators. -/
theorem universal_image_additivity_characterization {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Superop (Fin d) (Fin n)) (hT : IsChannel T) :
    (IsUniversalImageAdditive T ↔ IsImageAdditive T (id : Superop (Fin d) (Fin d))) ∧
    (IsImageAdditive T (id : Superop (Fin d) (Fin d)) ↔
      ∃ S : Superop (Fin d) (Fin d), IsChannel S ∧ IsEB S ∧ T = T ∘ S) ∧
    ((∃ S : Superop (Fin d) (Fin d), IsChannel S ∧ IsEB S ∧ T = T ∘ S) ↔
      ∃ S : Superop (Fin d) (Fin d), IsChannel S ∧ IsEssentialCQ S ∧ T = T ∘ S) ∧
    ((∃ S : Superop (Fin d) (Fin d), IsChannel S ∧ IsEssentialCQ S ∧ T = T ∘ S) ↔
      IsEssentialCQ T) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
