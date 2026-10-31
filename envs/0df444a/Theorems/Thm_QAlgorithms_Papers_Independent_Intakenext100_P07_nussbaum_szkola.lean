-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_nussbaum_szkola
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.nussbaum_szkola
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:45:22.770161+00:00
-- url     : https://prove2.me/theorems/06b8e533-fa02-48c5-b087-525be1d9a879
-- title:
--   §4.4.2 (4.91)–(4.93): Nussbaum–Szkoła representation
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Tildes denote sandwiched Rényi quantities and bars denote Petz quantities. Their trace functionals are $\widetilde Q_\alpha=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $\overline Q_\alpha=\operatorname{Tr}(\rho^\alpha\sigma^{1-\alpha})$; the divergences include division by $\operatorname{Tr}\rho$ inside the logarithm. Matrix powers vanish on the kernel, including power zero. The notation $\rho\ll\sigma$ means support inclusion.
--
--   Given actual spectral data for normalized ρ,σ, P(x,y)=λx|<ex|fy>|²,Q(x,y)=μy|<ex|fy>|² are probabilities, Dbarα(ρ||σ)=Dα(P||Q), support inclusion is equivalent, and the constructed laws tensorize.
--
--   $$
--   P(x,y)=\lambda_x|\langle e_x,f_y\rangle|^2,\quad Q(x,y)=\mu_y|\langle e_x,f_y\rangle|^2,\quad\overline D_\alpha(\rho\|\sigma)=D_\alpha(P\|Q).
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 70, §4.4.2 (4.91)–(4.93): Nussbaum–Szkoła representation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#4.ns
§4.4.2 (4.91)–(4.93): Nussbaum–Szkoła representation, arXiv:1504.00233v5, PDF p.70. -/
theorem nussbaum_szkola [Nonempty I] [Nonempty J] (r s : paperMat I) (hr : IsDensityMatrix r) (hs : IsDensityMatrix s)
    (v w : I → ℝ) (U V : paperMat I) (hv : SpectralRep r v U) (hw : SpectralRep s w V) :
    paperProbability (paperNsP v U V) ∧ paperProbability (paperNsQ w U V) ∧
    (∀ a : ℝ, 0 ≤ a → paperRenyi false r s (ENNReal.ofReal a) = paperRenyi false
      (Matrix.diagonal (fun xy => (paperNsP v U V xy:ℂ))) (Matrix.diagonal (fun xy => (paperNsQ w U V xy:ℂ))) (ENNReal.ofReal a)) ∧
    (paperSupported r s ↔ ∀ xy, 0 < paperNsP v U V xy → 0 < paperNsQ w U V xy) ∧
    (∀ r' s' : paperMat J, IsDensityMatrix r' → IsDensityMatrix s' → ∀ v' w' : J → ℝ, ∀ U' V' : paperMat J,
      SpectralRep r' v' U' → SpectralRep s' w' V' → ∀ i j : I, ∀ k l : J,
      paperNsP (fun ik : I × J => v ik.1*v' ik.2) (Matrix.kronecker U U') (Matrix.kronecker V V') ((i,k),(j,l)) = 
        paperNsP v U V (i,j)*paperNsP v' U' V' (k,l)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
