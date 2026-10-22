-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P01_finiteGroup_irrep_measurement
-- name    : QAlgorithms.Papers.Independent.Gap20.P01.finiteGroup_irrep_measurement
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:12:23.929884+00:00
-- url     : https://prove2.me/theorems/864389c0-b5a7-4b78-addb-a649896b73e8
-- title:
--   Finite-group Fourier extraction measures the irrep label
-- statement:
--   Let $G$ be a finite group and let $\{r_\mu\}_{\mu\in\widehat G}$ be a complete set of inequivalent irreducible unitary complex representations, of positive dimensions $d_\mu$. Let $R$ be a finite-dimensional unitary representation with a complete orthonormal reducing basis $|\mu,j,k\rangle_R$, where $1\le j\le n_\mu$ and $1\le k\le d_\mu$; multiplicities $n_\mu=0$ are allowed. For a normalized physical input, write $|\psi\rangle=\sum_{\mu,j,k}c_{\mu,j,k}|\mu,j,k\rangle_R$.
--
--   Use the explicitly corrected Fourier matrix $F^-_{(\rho,\alpha,\beta),g}=\sqrt{d_\rho/|G|}\,r_\rho(g^{-1})_{\alpha\beta}$, initialize the auxiliary register in its trivial-irrep coefficient, and apply $(F^-\otimes I)\,\mathrm{C}R\,((F^-)^\dagger\otimes I)$, with $\mathrm{C}R=\sum_g|g\rangle\langle g|\otimes R(g)$. Then
--
--   $$
--   \Pr[\text{auxiliary irrep label}=\mu]=\sum_{j=1}^{n_\mu}\sum_{k=1}^{d_\mu}|c_{\mu,j,k}|^2.
--   $$
--
--   The Fourier matrix and the extraction are unitary, and inverse Fourier transformation of the initialized coefficient gives the normalized uniform group vector. Also $F^-_{\rho,\alpha,\beta;g}=\overline{F^+_{\rho,\beta,\alpha;g}}$, where $F^+$ is the printed Fourier matrix. Thus gatewise conjugation and interchange of the padded row and column registers provide the corrected primitive; no group-inversion oracle is needed. The construction is a fixed composition of supplied Fourier, inverse Fourier and controlled-representation primitives and gives efficient irrep measurement whenever these primitives are efficient. It asserts the measured effects and probabilities, without asserting preservation of the input vector within an irrep.
-- source:
--   Efficient Quantum Circuits for Schur and Clebsch-Gordan Transforms, arXiv:quant-ph/0407082v4, PDF p. 3, Fig.3 and PDF p.4 probability paragraph after Eq.(11)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Gap20.P01

open QAlgorithms.Papers.Independent.Support21.P09 (Rep UnitaryRep elementaryGates)

variable {G L I : Type} [Group G] [Fintype G] [Fintype L]
  [Fintype I]

/-- PDF pp.3--4, Fig.3 and the probability paragraph after Eq.(11): irrep
measurement with exactly the source's Born probabilities. The conclusion
also gives the gatewise-conjugation/row-swap realization of Fminus from
Fplus. Thus efficient Fourier, inverse Fourier and controlled-R primitives
suffice; no new inversion oracle is assumed. The g-inverse correction of
the printed Eq.(7) is explicit; the literal printed output identity is deferred.
Only the measured probabilities are asserted, not a nondemolition instrument. -/
theorem finiteGroup_irrep_measurement (D : FiniteDual G L)
    (R : Rep G I) (hR : UnitaryRep R) (B : ReducingBasis D R) :
    (fourierMinus D)ᴴ * fourierMinus D = 1 ∧
    fourierMinus D * (fourierMinus D)ᴴ = 1 ∧
    (∀ a g, fourierMinus D a g =
      conj (fourierPlus D ⟨a.1, (a.2.2, a.2.1)⟩ g)) ∧
    applyRect (fourierMinus D)ᴴ (auxiliaryStart D) =
      WithLp.toLp 2 (fun _ : G => ((Real.sqrt (Fintype.card G))⁻¹ : ℂ)) ∧
    (figureThree D R)ᴴ * figureThree D R = 1 ∧
    ∀ psi : EuclideanSpace ℂ I, IsState psi → ∀ mu : L,
      probEvent (act (figureThree D R) (tensorVec (auxiliaryStart D) psi))
        (fun z => z.1.1 = mu) =
      ∑ j : Fin (B.multiplicity mu), ∑ k : Fin (D.irrep mu).dim,
        Complex.normSq (reducingCoefficients D R B psi ⟨mu, (j, k)⟩) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P01

end
