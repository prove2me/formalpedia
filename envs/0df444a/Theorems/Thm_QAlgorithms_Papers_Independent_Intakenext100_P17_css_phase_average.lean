-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P17_css_phase_average
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P17.css_phase_average
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:18:56.689985+00:00
-- url     : https://prove2.me/theorems/15e77b6e-3edd-4619-a3cc-791d2ad31960
-- title:
--   Averaging the withheld CSS phase gives a uniform coset mixture
-- statement:
--   Let $C_2\le C_1\le\mathbb F_2^n$ be binary linear codes. Fix a representative $v\in C_1$ and a shift $x\in\mathbb F_2^n$. For each $z\in\mathbb F_2^n$, define the normalized CSS vector
--
--   $$
--   |\psi_{v,x,z}\rangle=|C_2|^{-1/2}\sum_{w\in C_2}(-1)^{z\cdot w}|x+v+w\rangle,
--   $$
--
--   where the dot product and addition are over $\mathbb F_2$. If $z$ is uniform and its value is withheld, its average density operator is
--
--   $$
--   2^{-n}\sum_{z\in\mathbb F_2^n}|\psi_{v,x,z}\rangle\langle\psi_{v,x,z}|=
--   \frac1{|C_2|}\sum_{w\in C_2}|v+w+x\rangle\langle v+w+x|.
--   $$
--
--   This is the mixture of computational words obtained by selecting $w$ uniformly from $C_2$. It removes the unused phase label from the preparation without equating protocols that publicly retain that label.
-- source:
--   Simple Proof of Security of the BB84 Quantum Key Distribution Protocol, arXiv:quant-ph/0003004v2, PDF p. 4, Equation (4): averaging the unused CSS phase label

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P17

namespace QAlgorithms.Papers.Independent.Intakenext100.P17

noncomputable section

open scoped ComplexConjugate

open Classical

open QAlgorithms.DopedTomography (bellVector)

open QAlgorithms.Papers.Independent.Support50.P04 (BinaryWord)

/-- PDF p.4, Eq.(4): averaging the independent, uniform and undisclosed phase
label z removes all cross terms and gives the uniform computational coset mixture.
The key label is a fixed representative v in C1, not an assumed literal
coset-invariant vector for nonzero z. The equation is an equality of density
operators; no claim about a public register retaining z is made. -/
theorem css_phase_average {n : ℕ}
    (C1 C2 : Submodule (ZMod 2) (BinaryWord n)) (h21 : C2 ≤ C1)
    (v : C1) (x : BinaryWord n) :
    ((2 : ℂ) ^ n)⁻¹ •
        (∑ z : BinaryWord n, pureDensity (cssPhaseWord C2 (v : BinaryWord n) x z)) =
      (Fintype.card C2 : ℂ)⁻¹ •
        (∑ w : C2, pureDensity
          (ket (bitsOfZMod ((v : BinaryWord n) + (w : BinaryWord n) + x)))) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P17
