-- Prove2me | Theorems.Thm_RandomReservoir_Static_lemma_1
-- name    : RandomReservoir.Static.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:25.399658+00:00
-- url     : https://prove2.me/theorems/75291393-7e4c-490c-b2ad-eb8f7f915034
-- title:
--   Lemma 1, p. 37 — the random ReLU network H_W^{A,ζ} is product-measurable in (ω, z)
-- statement:
--   Let $\mathcal X$ be a separable real Hilbert space with its Borel $\sigma$-algebra $\mathcal B(\mathcal X)$, and let $(\Omega,\mathcal F)$ be a measurable space. Let $A=(A_1,\dots,A_N):\Omega\to\mathcal X^N$, $\zeta:\Omega\to\mathbb R^N$ and $W:\Omega\to\mathbb M_{m,N}$ be measurable. Then the random ReLU network
--   $$(\omega,z)\longmapsto H_{W(\omega)}^{A(\omega),\zeta(\omega)}(z)=W(\omega)\,\sigma\big(A(\omega)z+\zeta(\omega)\big)\in\mathbb R^m$$
--   is $\mathcal F\otimes\mathcal B(\mathcal X)$-measurable.
--
--   In particular $H_W^{A,\zeta}(Z)$ is a random variable for every $\mathcal X$-valued random variable $Z$, which is what makes the expectations in Theorem 1 well defined.
--
--   **Formalization Note.** The readout $W(\omega)$ is given by its entries, as a measurable map into $\mathbb R^{m\times N}$ with the product $\sigma$-algebra.
-- source:
--   Gonon, Grigoryeva & Ortega, Ann. Appl. Probab. 33 (2023), Lemma 1, p. 37

import Mathlib
import Definitions.Def_RandomReservoir_Static_Setting

namespace RandomReservoir.Static

open MeasureTheory

/-- Lemma 1, Gonon–Grigoryeva–Ortega, Ann. Appl. Probab. 33 (2023), p. 37: for random inner weights
`A = (A_1, …, A_N)`, `ζ` and a random readout `W` on a measurable space `Ω`, the map
`(ω, z) ↦ H_{W(ω)}^{A(ω), ζ(ω)}(z)` is `𝓕 ⊗ 𝓑(𝒳)`-measurable. -/
theorem lemma_1
    {𝒳 : Type*} [NormedAddCommGroup 𝒳] [InnerProductSpace ℝ 𝒳] [CompleteSpace 𝒳]
    [TopologicalSpace.SeparableSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    {Ω : Type*} [MeasurableSpace Ω] (m N : ℕ)
    (A : Ω → Fin N → 𝒳) (hA : Measurable A) (ζ : Ω → Fin N → ℝ) (hζ : Measurable ζ)
    (W : Ω → Fin m → Fin N → ℝ) (hW : Measurable W) :
    Measurable (fun p : Ω × 𝒳 => network (Matrix.of (W p.1)) (fun i => (A p.1 i, ζ p.1 i)) p.2) := by sorry

end RandomReservoir.Static
