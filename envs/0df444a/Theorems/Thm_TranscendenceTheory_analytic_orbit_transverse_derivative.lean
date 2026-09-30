-- Prove2me | Theorems.Thm_TranscendenceTheory_analytic_orbit_transverse_derivative
-- name    : TranscendenceTheory.analytic_orbit_transverse_derivative
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T19:01:25.867977+00:00
-- url     : https://prove2.me/theorems/22a35d23-3c42-43d4-ba46-2a1cab4b6f76
-- title:
--   A finite-order analytic orbit supplies a transverse derivative
-- statement:
--   Let $R$ be a commutative $\mathbb Q$-algebra, $D:R\to R$ a $\mathbb Q$-derivation, and $\mathfrak p$ an ideal of $R$. Let $\Phi:R\to (\mathbb C\to\mathbb C)$ be an algebra homomorphism, with pointwise operations on the target, and fix $z_0\in\mathbb C$.
--
--   Assume that for every $r\in R$, the functions $\Phi(Dr)$ and $(\Phi r)'$ agree on some neighbourhood of $z_0$, and that $\Phi r(z_0)=0$ for every $r\in\mathfrak p$. Suppose $f\in\mathfrak p$, the function $\Phi f$ is analytic at $z_0$, and its analytic order there is finite.
--
--   Then there exist natural numbers $N,k$ such that
--
--   $$
--   \operatorname{ord}_{z_0}(\Phi f)=N,\qquad
--   0\le k<N,\qquad D^k f\in\mathfrak p,\qquad D^{k+1}f\notin\mathfrak p.
--   $$
--
--   Thus $q=D^k f$ is a transverse equation: $q\in\mathfrak p$ and $Dq\notin\mathfrak p$. In particular $N\ge1$. The ideal need not be prime and the ring need not be Noetherian for this theorem.
--
--   **Formalization Note.** This is a one-direction analytic criterion supporting the transverse-equation step of the zero-estimate argument in [Philippon (1986), Lemma 4.6 and Proposition 4.7, pp. 378–379](https://www.numdam.org/item/10.24033/bsmf.2060.pdf). It is not a formalization of the full tangent-rank assertion of Lemma 4.6. The formal proof uses the Taylor-order characterization in the pinned Mathlib version. Orbit construction for the chosen geometric components and the global degree estimate are separate obligations.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Lemma 4.6, p. 378, and Proposition 4.7, pp. 378-379. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. One-direction analytic auxiliary criterion for the transverse equation: a nonzero analytic germ on an orbit through the prime yields a first derivative leaving it. This is not the full tangent-rank assertion of Lemma 4.6. Taylor-order characterization: Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Analysis/Analytic/Order.lean, analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero. Geometric orbit and prime selection and the total degree budget remain open.

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic

open scoped Topology

theorem TranscendenceTheory.analytic_orbit_transverse_derivative
    (R : Type*) [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p : Ideal R)
    (φ : R →ₐ[ℚ] (ℂ → ℂ)) (z : ℂ)
    (hD : ∀ r, φ (D r) =ᶠ[𝓝 z] deriv (φ r))
    (hzero : ∀ r ∈ p, φ r z = 0)
    (f : R) (hf : f ∈ p) (hanalytic : AnalyticAt ℂ (φ f) z)
    (hfinite : analyticOrderAt (φ f) z ≠ ⊤) :
    ∃ n k : ℕ, analyticOrderAt (φ f) z = (n : ℕ∞) ∧ k < n ∧
      (D^[k]) f ∈ p ∧ (D^[k + 1]) f ∉ p := by sorry
