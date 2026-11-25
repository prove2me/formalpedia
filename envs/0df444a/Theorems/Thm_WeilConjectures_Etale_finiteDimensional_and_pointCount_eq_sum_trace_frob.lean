-- Prove2me | Theorems.Thm_WeilConjectures_Etale_finiteDimensional_and_pointCount_eq_sum_trace_frob
-- name    : WeilConjectures.Etale.finiteDimensional_and_pointCount_eq_sum_trace_frob
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-25T12:41:07.939414+00:00
-- url     : https://prove2.me/theorems/f71039b8-cefe-566d-a7af-9d3c7d121441
-- title:
--   Finiteness of $H^i(X_{\bar k},\mathbb Q_\ell)$ and the Lefschetz trace formula $N_m=\sum_i(-1)^i\operatorname{Tr}(F^{*m}\mid H^i)$
-- statement:
--   Let $k=\mathbb F_q$ be a finite field of characteristic $p$, $X$ a smooth, projective, geometrically irreducible $k$-scheme of dimension $d$ (structure morphism $f$), and $\ell\ne p$ a prime. Then
--
--   1. every $\ell$-adic cohomology group $H^i(X_{\bar k},\mathbb Q_\ell)$ is a finite-dimensional $\mathbb Q_\ell$-vector space;
--   2. (**Grothendieck–Lefschetz trace formula**) for every $m\ge 1$, the number $N_m$ of $\mathbb F_{q^m}$-points of $X$ satisfies
--   $$N_m=\sum_{i=0}^{2d}(-1)^i\operatorname{Tr}\big((F^*)^m\mid H^i(X_{\bar k},\mathbb Q_\ell)\big),$$
--   where $F^*$ is the endomorphism induced by the relative Frobenius of $X_{\bar k}$.
--
--   The cohomology groups, $F^*$ and $N_m$ are those of the definitions `WeilConjectures_Etale_Coefficients`, `WeilConjectures_Etale_WeilData` and `WeilConjectures_zetaFunction`.
--
--   **Formalization note.** As in the mission's statements, $k$ lives in `Type` and $X$ in `Scheme.{0}`; the étale sheaves take values in abelian groups of universe $1$. $N_m$ is `WeilConjectures.pointCount p f m` (the number of morphisms $\operatorname{Spec}\mathbb F_{q^m}\to X$ over $k$). Finite-dimensionality is asserted for every $i$, while the sum runs over $0\le i\le 2d$.
-- source:
--   P. Deligne, Cohomologie étale (SGA 4½), « Rapport sur la formule des traces »; P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), (1.5); A. Grothendieck, Formule de Lefschetz et rationalité des fonctions L, Séminaire Bourbaki 279 (1964/65).

import Mathlib
import Definitions.Def_FiniteFields_Etale_Cohomology
import Definitions.Def_FiniteFields_Etale_ConstantPullback
import Definitions.Def_FiniteFields_Etale_ExactPullback
import Definitions.Def_FiniteFields_Etale_FiniteCoefficients
import Definitions.Def_FiniteFields_Etale_Functoriality
import Definitions.Def_FiniteFields_Etale_Sites
import Definitions.Def_FiniteFields_Schemes_GeneralFrobenius
import Definitions.Def_WeilConjectures_Etale_BaseChange
import Definitions.Def_WeilConjectures_Etale_Coefficients
import Definitions.Def_WeilConjectures_Etale_Pullback
import Definitions.Def_WeilConjectures_Etale_WeilData

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FiniteFields.Etale
open WeilConjectures.Etale
variable {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) (ℓ : ℕ) [Fact ℓ.Prime]

theorem WeilConjectures.Etale.finiteDimensional_and_pointCount_eq_sum_trace_frob (d : ℕ) [SmoothOfRelativeDimension d f] [GeometricallyIrreducible f]
    (hproj : WeilConjectures.IsProjectiveOver k f) (hℓ : ℓ ≠ p) :
    (∀ i, FiniteDimensional ℚ_[ℓ] (Hrat ℓ (geom f) i)) ∧
    (∀ m, 1 ≤ m → (pointCount p f m : ℚ_[ℓ]) =
      ∑ i ∈ Finset.range (2 * d + 1),
        (-1) ^ i * LinearMap.trace ℚ_[ℓ] (Hrat ℓ (geom f) i) (Frob p f ℓ i ^ m)) := by sorry
