-- Prove2me | Theorems.Thm_TranscendenceTheory_exists_reduced_bivariate_model
-- name    : TranscendenceTheory.exists_reduced_bivariate_model
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T09:51:45.257487+00:00
-- url     : https://prove2.me/theorems/986532db-5193-4e05-8e27-b15b73b1fda8
-- title:
--   Unique reduced polynomial representatives in an integral simple extension
-- statement:
--   Let $\theta,\nu\in\mathbb C$, with $\theta$ transcendental over $\mathbb Q$ and $\nu$ integral over $\mathbb Z[\theta]$. Write $\operatorname{ev}(p)=p(\theta,\nu)$ for evaluation on $\mathbb Z[X,Y]$.
--
--   There is a monic polynomial $g\in\mathbb Z[X,Y]$, monic in $Y$ and of positive $Y$-degree $r$, such that
--
--   $$
--   \operatorname{ev}(p)=0\quad\Longleftrightarrow\quad g\mid p
--   \qquad(p\in\mathbb Z[X,Y]).
--   $$
--
--   Moreover, every polynomial $p$ has exactly one representative $q$ with
--
--   $$
--   \deg_Y q<r,\qquad q(\theta,\nu)=p(\theta,\nu).
--   $$
--
--   In particular, evaluation is injective on polynomials of $Y$-degree less than $r$. This justifies using nonzero symbolic coefficient vectors as nonzero complex coefficient vectors in an auxiliary-function construction. The integer coefficient ring is retained; no new denominator is introduced.
--
--   **Formalization Note.** The outer polynomial variable is $Y$, and natural degree assigns degree zero to the zero polynomial. Positive $r$ includes its unique zero representative.
-- source:
--   Senthil Kumar K (2026), Section 3, opening reduced representation and the integer double sum immediately before Lemma 1. This states the integral-ring normal-form part, with a fixed denominator already cleared; it makes no claim about normalization of general rational-function denominators. The minimal-polynomial kernel theorem is Mathlib minpoly.isIntegrallyClosed_dvd_iff, FieldTheory/Minpoly/IsIntegrallyClosed.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474. https://www.cambridge.org/core/journals/proceedings-of-the-edinburgh-mathematical-society/article/algebraic-independence-of-values-of-weierstrass-elliptic-and-zeta-functions/E91A8EEEB1F63536D95D1DE7D7DD47E2

import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open Polynomial Module
open scoped Polynomial

theorem TranscendenceTheory.exists_reduced_bivariate_model (θ ν : ℂ) (hθ : Transcendental ℚ θ)
    (hν : ∃ f : ℤ[X][X], f.Monic ∧ f.eval₂ (aeval θ).toRingHom ν = 0) :
    ∃ g : ℤ[X][X], g.Monic ∧ 0 < g.natDegree ∧
      (∀ p : ℤ[X][X], p.eval₂ (aeval θ).toRingHom ν = 0 ↔ g ∣ p) ∧
      (∀ p : ℤ[X][X], ∃! q : ℤ[X][X], q.natDegree < g.natDegree ∧
        q.eval₂ (aeval θ).toRingHom ν = p.eval₂ (aeval θ).toRingHom ν) := by sorry
