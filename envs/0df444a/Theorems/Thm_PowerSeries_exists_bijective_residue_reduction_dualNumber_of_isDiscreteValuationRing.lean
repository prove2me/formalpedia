-- Prove2me | Theorems.Thm_PowerSeries_exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing
-- name    : PowerSeries.exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/ad0fcb1f-523b-5ffe-942d-851cc905ea32
-- title:
--   Reduction tower and τ : O[[X]]/𝔪² → k[ε]
-- statement:
--   Let $O$ be a commutative ring which is a local domain and a discrete valuation ring, with residue field $k =$ `ResidueField O` and residue map `residue O`, and write $R = O⟦X⟧$ for the power series ring and $\mathfrak m$ for its maximal ideal. The assertion is the existence of the following data. First, a ring homomorphism $\iota_0 : R/\mathfrak m^{0+1} \to k$ which is bijective and satisfies $\iota_0 \circ (\text{reduction} \circ (O \to R)) = \mathrm{residue}_O$, so that the structure map identifies $R/\mathfrak m$ with $k$ compatibly with $O \to k$. Secondly, for every $n \in \mathbb N$ a ring homomorphism $\pi_n : R/\mathfrak m^{n+2} \to R/\mathfrak m^{n+1}$ with $\pi_n \circ \mathrm{mk}_{\mathfrak m^{n+2}} = \mathrm{mk}_{\mathfrak m^{n+1}}$, i.e. the canonical reductions along the tower. Thirdly, a ring homomorphism $\tau : R/\mathfrak m^{2} \to k[\varepsilon]$, the dual numbers over $k$, such that: $\tau$ restricted along $O \to R \to R/\mathfrak m^2$ equals $O \to k \hookrightarrow k[\varepsilon]$; $\tau$ sends the class of $X$ to $\varepsilon$; $\tau$ is surjective; the product of $\ker \tau$ with the image of $\mathfrak m$ in $R/\mathfrak m^2$ is the zero ideal; composing $\tau$ with the projection $k[\varepsilon] \to k$ onto the first coordinate gives $\iota_0 \circ \pi_0$; and $\tau$ is the unique ring homomorphism $R/\mathfrak m^2 \to k[\varepsilon]$ with the first two of these properties.
--
--   This collects the elementary local algebra of $O⟦X⟧$ over a discrete valuation ring $O$: the identification of $R/\mathfrak m$ with the residue field $k$, the canonical tower of reductions $R/\mathfrak m^{n+2} \to R/\mathfrak m^{n+1}$, and the unique $O$-compatible surjection $R/\mathfrak m^2 \twoheadrightarrow k[\varepsilon]$ sending $X$ to $\varepsilon$, which realises $k[\varepsilon]$ as the first infinitesimal deformation quotient. It is used in the construction of power series towers for fake elliptic curves in the Čerednik–Drinfel'd part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem PowerSeries.exists_bijective_residue_reduction_dualNumber_of_isDiscreteValuationRing
    (O : Type) [CommRing O] [IsLocalRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    ∃ (ι₀ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (0 + 1)) →+* ResidueField O) (hι₀ : Function.Bijective ι₀)
      (hι₀O : ι₀.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (0 + 1))).comp (algebraMap O (PowerSeries O))) = residue O)
      (π : ∀ n : ℕ, (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1 + 1)) →+* (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (n + 1)))
      (hπ : ∀ n, (π n).comp (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1 + 1))) = Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (n + 1)))
      (τ : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O)),
      τ.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
          (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O) ∧
      τ (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps ∧
      Function.Surjective τ ∧
      RingHom.ker τ * (maximalIdeal (PowerSeries O)).map (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))) = ⊥ ∧
      (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom.comp τ = ι₀.comp (π 0) ∧
      ∀ τ' : (PowerSeries O ⧸ maximalIdeal (PowerSeries O) ^ (1 + 1)) →+* DualNumber (ResidueField O),
        τ'.comp ((Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1))).comp (algebraMap O (PowerSeries O))) =
            (algebraMap (ResidueField O) (DualNumber (ResidueField O))).comp (residue O) →
        τ' (Ideal.Quotient.mk (maximalIdeal (PowerSeries O) ^ (1 + 1)) PowerSeries.X) = DualNumber.eps →
        τ' = τ := by sorry
