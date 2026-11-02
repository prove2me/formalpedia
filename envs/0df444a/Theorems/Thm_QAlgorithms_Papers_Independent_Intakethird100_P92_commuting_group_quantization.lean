-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P92_commuting_group_quantization
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P92.commuting_group_quantization
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:25:28.250111+00:00
-- url     : https://prove2.me/theorems/95bf093c-948d-4953-844c-6a923b4e3028
-- title:
--   A commuting group action descends to a continuous unitary representation
-- statement:
--   Let $(E,E_+,\theta)$ be a reflection-positive complex Hilbert space and let $U$ be a strongly continuous unitary representation of a topological group $G$ on $E$. Assume $U(g)E_+\subseteq E_+$ and $U(g)\theta=\theta U(g)$ for every $g\in G$. There is a strongly continuous unitary representation $\widehat U$ on the canonical OS space such that
--   $$\widehat U(g)q(v)=q(U(g)v)\quad(g\in G,\ v\in E_+).$$
--   The induced operators satisfy the identity and multiplication laws. This is the OS quantization of the given representation, characterized on the dense canonical quotient image.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, PDF p. 9, Proposition 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal

open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E}

/-- Proposition 2.5, PDF p. 9, for an arbitrary topological group. The induced
unitary representation is required to agree with the canonical quotient on every
input, so it is the OS representation, rather than an unrelated representation. -/
theorem commuting_group_quantization [hHilbert : CompleteSpace E] (r : ReflectionData E)
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : G → E ≃ₗᵢ[ℂ] E)
    (hOne : ∀ x, U 1 x = x)
    (hMul : ∀ g h x, U (g * h) x = U g (U h x))
    (hContinuous : ∀ x, Continuous (fun g => U g x))
    (hPlus : ∀ g, ∀ x ∈ r.plus, U g x ∈ r.plus)
    (hTheta : ∀ g x, U g (r.theta x) = r.theta (U g x)) :
    ∃ V : G → OS r ≃ₗᵢ[ℂ] OS r,
      (∀ x, V 1 x = x) ∧
      (∀ g h x, V (g * h) x = V g (V h x)) ∧
      (∀ x, Continuous (fun g => V g x)) ∧
      (∀ g v, V g (osQ r v) = osQ r ⟨U g v, hPlus g v v.property⟩) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P92

end
