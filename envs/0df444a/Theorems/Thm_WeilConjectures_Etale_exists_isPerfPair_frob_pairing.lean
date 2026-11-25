-- Prove2me | Theorems.Thm_WeilConjectures_Etale_exists_isPerfPair_frob_pairing
-- name    : WeilConjectures.Etale.exists_isPerfPair_frob_pairing
-- status  : Open
-- author  : @Idealson
-- created : 2026-11-25T12:48:37.274338+00:00
-- url     : https://prove2.me/theorems/9bd03812-2124-5010-96ec-1c64a9dfb5bd
-- title:
--   Poincaré duality for $\ell$-adic cohomology: perfect pairings $H^i\times H^{2n-i}\to\mathbb Q_\ell$ with $\langle F^*x,F^*y\rangle=q^n\langle x,y\rangle$
-- statement:
--   Let $k=\mathbb F_q$ be a finite field of characteristic $p$, $Y$ a smooth, projective, geometrically irreducible $k$-scheme of dimension $n$ (structure morphism $f$), and $\ell\ne p$ a prime. Then there are $\mathbb Q_\ell$-bilinear pairings
--   $$\langle\cdot,\cdot\rangle_i\colon H^i(Y_{\bar k},\mathbb Q_\ell)\times H^{2n-i}(Y_{\bar k},\mathbb Q_\ell)\to\mathbb Q_\ell\qquad(i\in\mathbb N)$$
--   such that, for every $0\le i\le 2n$, the pairing $\langle\cdot,\cdot\rangle_i$ is perfect and
--   $$\langle F^*x,F^*y\rangle_i=q^n\,\langle x,y\rangle_i\qquad(x\in H^i,\ y\in H^{2n-i}),$$
--   where $F^*$ is the endomorphism induced by the relative Frobenius of $Y_{\bar k}$.
--
--   This is Poincaré duality (cup product followed by the trace $H^{2n}(Y_{\bar k},\mathbb Q_\ell)\cong\mathbb Q_\ell(-n)$) together with the fact that $F^*$ acts on $H^{2n}$ by multiplication by $q^n$.
--
--   **Formalization note.** As in the mission's statements, $k$ lives in `Type` and $Y$ in `Scheme.{0}`. The family of pairings is indexed by all $i\in\mathbb N$ but constrained only for $i\le 2n$ (for $i>2n$ the truncated difference $2n-i$ is $0$); the pairings are asserted to exist, not specified.
-- source:
--   P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), §2, Théorème (2.3) with (2.5); E. Freitag, R. Kiehl, Étale Cohomology and the Weil Conjecture, Chapter II, §1 (Poincaré duality, 1.13–1.14); SGA 4, Exposés XVII–XVIII.

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

open CategoryTheory AlgebraicGeometry
open WeilConjectures.Etale

theorem WeilConjectures.Etale.exists_isPerfPair_frob_pairing {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (.of k)) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    [SmoothOfRelativeDimension n f] [GeometricallyIrreducible f]
    (hproj : WeilConjectures.IsProjectiveOver k f) (hℓ : ℓ ≠ p) :
    ∃ pair : ∀ i, Hrat ℓ (geom f) i →ₗ[ℚ_[ℓ]] Hrat ℓ (geom f) (2 * n - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
      (∀ i ≤ 2 * n, (pair i).IsPerfPair) ∧
      ∀ i ≤ 2 * n, ∀ x y, pair i (Frob p f ℓ i x) (Frob p f ℓ (2 * n - i) y) =
        (Nat.card k : ℚ_[ℓ]) ^ n * pair i x y := by sorry
